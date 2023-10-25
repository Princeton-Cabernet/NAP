import os
import re
import sys
import glob
import errno
import math
import json
import pickle
import argparse
import traceback
import ipaddress
import time
import shutil
import dateutil.relativedelta
from datetime import datetime as dt

import pyspark
import pickle
from pyspark.sql import SparkSession
from pyspark.sql.types import *
import pyspark.sql.functions as F

import pandas as pd
import numpy as np
from scipy import stats
from scipy.sparse import csr_matrix
import multiprocessing as mp
import matplotlib.pyplot as plt

from global_variables import all_header_titles

# Public variables
FIVE_TUPLE = ["src_ip","dst_ip","src_port","dst_port","protocol"]
COLOR_LIST = ["red","blue","orange","green","purple","yellow","pink","black"]

# Output directory
WH_DIRECTORY = "/mnt/anonflow/catql/"

# Window size
WINDOW_SIZE_IN_NANOSEC = 1 * (10**9)
TARGET_TIME_IN_NANOSEC = 60 * (10**9)

# Home netmask
HOME_NET = ["128.112.0.0/16","140.180.0.0/16","204.153.48.0/23","66.180.176.0/24","66.180.177.0/24","66.180.180.0/22"]

# Print functions
def prRed(skk): print("\033[91m {}\033[00m" .format(skk))
def prGreen(skk): print("\033[92m {}\033[00m" .format(skk))
def prYellow(skk): print("\033[93m {}\033[00m" .format(skk))

# Spark configuration
conf = pyspark.SparkConf().setAll([('spark.cores.max', '180'), ('spark.driver.memory','200g'), 
                                   ("spark.default.parallelism", '180'), 
                                   ("spark.speculation","false"), 
                                   ("spark.sql.warehouse.dir", WH_DIRECTORY), 
                                   ("spark.driver.maxResultSize", "50g"),
                                   ("spark.ui.showConsoleProgress", "false")])
spark = SparkSession.builder.appName('p4-ml-ids').config(conf=conf).getOrCreate()
sc = spark.sparkContext

# Preprocess HOME_NET to identify external IPs later
internal_ips = []
for item in HOME_NET:
    num_bits = 32 - int(item.split("/")[1])
    internal_ips.append((int(ipaddress.IPv4Address(item.split("/")[0])), (2**32-1) >> num_bits << num_bits))

bc_internal_ips = sc.broadcast(internal_ips)    

def is_internal_func(ip, broadcast_dict):
    internal_ips = broadcast_dict.value
    for item in internal_ips:
        if item[1] & int(ip) == item[0]:
            return True
    return False

def mac_to_int_func(mac):
    return int(re.sub('[:\.\-\s]', '', mac), 16)

# ip_to_int converts IP from string form to int form
ip_to_int = F.udf(lambda ip: int(ipaddress.IPv4Address(ip)), LongType())

# is_internal returns True if ip is internal and False otherwise
is_internal = F.udf(lambda ip : is_internal_func(ip, bc_internal_ips), BooleanType())

# ip_to_int converts mac from string form to int form
mac_to_int = F.udf(lambda mac: mac_to_int_func(mac), LongType())


def preprocess_df(path):

    in_path = WH_DIRECTORY + path + "received_csvs/"
    df = spark.read.csv(in_path, inferSchema=True, header=False, sep="\\t")
    
    df.createOrReplaceTempView("tshark")
    header_fields = []
    for counter, item in enumerate(all_header_titles):
        header_fields.append(" {field} AS {title} ".format(field=df.schema[counter].name, title=item))
    select_q = "SELECT {fields} FROM tshark".format(fields=', '.join(header_fields))
    df = spark.sql(select_q)

    df = df.withColumn("report", mac_to_int(F.col("src_mac"))).\
            withColumn("mac_ts", mac_to_int(F.col("dst_mac"))).\
            drop("src_mac", "dst_mac").\
            where(F.col("mac_ts").isNotNull())
    df.cache()
    
    min_ts = df.agg(F.min(F.col("mac_ts")).alias("min_ts")).collect()[0]['min_ts']
    max_ts = df.agg(F.max(F.col("mac_ts")).alias("max_ts")).collect()[0]['max_ts']
    
    df = df.withColumn('window',((F.col("mac_ts")-min_ts)/WINDOW_SIZE_IN_NANOSEC).cast(IntegerType()))

    return df, min_ts, max_ts


def get_groundtruth(path, df, min_ts, max_ts):

    df = df.select(FIVE_TUPLE + ["report", "mac_ts", "window"]).\
            withColumn("source_ip_int", ip_to_int(F.col("src_ip"))).\
            withColumn("from_internal", is_internal(F.col("source_ip_int"))).\
            withColumn("external_ip", F.when(F.col("from_internal"), F.col("dst_ip")).otherwise(F.col("src_ip"))).\
            withColumn("internal_ip", F.when(F.col("from_internal"), F.col("src_ip")).otherwise(F.col("dst_ip"))).\
            drop("source_ip_int")
    df_insert = df.filter(F.col("from_internal")==True).select("window", "internal_ip", "external_ip","mac_ts")
    df_query = df.filter(F.col("from_internal")==False)
    df_insert.cache()
    df_query.cache()

    num_wins = math.ceil(TARGET_TIME_IN_NANOSEC / WINDOW_SIZE_IN_NANOSEC )
    df_query_drop = df_query
    df_insert_grouped = df_insert.groupBy("window", "internal_ip", "external_ip").\
                                  agg(F.min("mac_ts").alias("min_insert_mac_ts"),
                                      F.max("mac_ts").alias("max_insert_mac_ts"))

    for win in range(1, num_wins):
        df_insert_shifted = df_insert_grouped.withColumn("window", (F.col("window") + win))
        df_query_drop = df_query_drop.join(df_insert_shifted.select("window", "internal_ip", "external_ip"), 
                                           on = ["window", "internal_ip", "external_ip"], 
                                           how="left_anti")
    
    df_query_drop = df_query_drop.join(df_insert_grouped.select("window", "internal_ip", "external_ip", "min_insert_mac_ts"),
                                   on = ["window", "internal_ip", "external_ip"], 
                                   how="left").\
                              fillna(max_ts + 1).\
                              where(F.col("min_insert_mac_ts") - F.col("mac_ts") >= 0 ).\
                              drop("min_insert_mac_ts").\
                              join(df_insert_grouped.withColumn("window", (F.col("window") + num_wins)).\
                                                     select("window", "internal_ip", "external_ip", "max_insert_mac_ts"),
                                   on = ["window", "internal_ip", "external_ip"], 
                                   how="left").\
                              fillna(min_ts - TARGET_TIME_IN_NANOSEC - 1).\
                              where(F.col("mac_ts") - F.col("max_insert_mac_ts") > TARGET_TIME_IN_NANOSEC ).\
                              drop("max_insert_mac_ts").\
                              withColumn("groud_truth", F.lit(1))

    df_query_drop = df_query_drop.withColumnRenamed("window", "window").\
                                    withColumnRenamed("internal_ip", "internal_ip").\
                                    withColumnRenamed("external_ip", "external_ip").\
                                    withColumnRenamed("src_ip", "src_ip").\
                                    withColumnRenamed("dst_ip", "dst_ip").\
                                    withColumnRenamed("src_port", "src_port").\
                                    withColumnRenamed("dst_port", "dst_port").\
                                    withColumnRenamed("protocol", "protocol").\
                                    withColumnRenamed("report", "report").\
                                    withColumnRenamed("mac_ts", "mac_ts").\
                                    withColumnRenamed("from_internal", "from_internal").\
                                    withColumnRenamed("groud_truth", "groud_truth")
    
    df_comp = df.join(df_query_drop, on = df.columns, how="left").fillna(0)
    df_comp.cache()
    df_insert.unpersist()
    df_query.unpersist()
    df.unpersist()
    out_path = WH_DIRECTORY + path + "groundtruth_csvs/"
    if os.path.exists(out_path):
        shutil.rmtree(out_path)
    df_comp.write.csv(out_path, header="true")
    return df_comp
    
    
def agg_stats(path, df):

    df_comp_win = df.withColumn("num_falsepos", F.when(((F.col("report") == 0) & (F.col("groud_truth") == 1)), F.lit(1)).otherwise(F.lit(0))).\
                      withColumn("num_falseneg", F.when(((F.col("report") == 1) & (F.col("groud_truth") == 0)), F.lit(1)).otherwise(F.lit(0))).\
                      withColumn("num_truepos", F.when(((F.col("report") == 0) & (F.col("groud_truth") == 0)), F.lit(1)).otherwise(F.lit(0))).\
                      withColumn("num_trueneg", F.when(((F.col("report") == 1) & (F.col("groud_truth") == 1)), F.lit(1)).otherwise(F.lit(0))).\
                      groupBy("window").\
                      agg(F.sum("num_falsepos").alias("num_falsepos"),
                          F.sum("num_falseneg").alias("num_falseneg"),
                          F.sum("num_truepos").alias("num_truepos"),
                          F.sum("num_trueneg").alias("num_trueneg"),
                          F.sum("groud_truth").alias("num_negatives"),
                          F.sum(F.lit(1)).alias("num_packets")).\
                      withColumn("FPR", F.col("num_falsepos")/F.col("num_negatives"))
    
    out_path = WH_DIRECTORY + path + "plot_inputs/fpr.csv"
    if os.path.exists(out_path):
        shutil.rmtree(out_path)
    df_comp_win.coalesce(1).write.csv(out_path, header="true")
    df.unpersist()


def main(spark):
    suffixes = ["trial_0.5_12/", "trial_0.5_9/", "trial_0.5_6/", "trial_0.1_12/", "trial_0.9_12/"]
    paths = ["eval/sf/" + suf for suf in suffixes]
    
    idx = 0
    while idx < len(paths):
        try:
            t0 = dt.now()
            path = paths[idx]
            prGreen("Start processing %s..." % (path))
            df, min_ts, max_ts = preprocess_df(path)
            min_ts_dt = dt.fromtimestamp(min_ts/(10**9))
            max_ts_dt = dt.fromtimestamp(max_ts/(10**9))
            diff = dateutil.relativedelta.relativedelta(max_ts_dt, min_ts_dt)
            prGreen("The duration of the trace: %d days, %d hours, %d minutes and %d seconds" 
                    %(diff.days, diff.hours, diff.minutes, diff.seconds))
            df = get_groundtruth(path, df, min_ts, max_ts)
            agg_stats(path, df)
            idx = idx + 1
            prGreen("Processing complete: %d seconds\n" % ((dt.now()-t0).total_seconds()))
        except Exception as e:
            
            prRed("Path " + str(path) +" fails: " + str(e))
            time.sleep(3)
            out_path = WH_DIRECTORY + path + "groundtruth_csvs/"
            if os.path.exists(out_path):
                shutil.rmtree(out_path)
            out_path = WH_DIRECTORY + path + "plot_inputs/fpr.csv"
            if os.path.exists(out_path):
                shutil.rmtree(out_path)


if __name__ == "__main__":    
    main(spark)
