#!/bin/bash


tcpdump -r campus_trace_10min.pcap -C 1000MB -w  campus_trace_10min_sliced.pcap

python3 create_name_list.py ~/mnt/anonflow/catql/eval/sf/trial_0.5_6/received_pcaps > names.list
bash get_header_fields.sh
mv  ~/mnt/anonflow/catql/eval/sf/trial_0.5_6/received_pcaps/*.csv ~/mnt/anonflow/catql/eval/sf/trial_0.5_6/received_csvs/
echo "Done with trial 0.5_6 (1/5)"

python3 create_name_list.py ~/mnt/anonflow/catql/eval/sf/trial_0.5_9/received_pcaps > names.list
bash get_header_fields.sh
mv  ~/mnt/anonflow/catql/eval/sf/trial_0.5_9/received_pcaps/*.csv ~/mnt/anonflow/catql/eval/sf/trial_0.5_9/received_csvs/
echo "Done with trial 0.5_9 (2/5)"

python3 create_name_list.py ~/mnt/anonflow/catql/eval/sf/trial_0.5_12/received_pcaps > names.list
bash get_header_fields.sh
mv  ~/mnt/anonflow/catql/eval/sf/trial_0.5_12/received_pcaps/*.csv ~/mnt/anonflow/catql/eval/sf/trial_0.5_12/received_csvs/
echo "Done with trial 0.5_12 (3/5)"

python3 create_name_list.py ~/mnt/anonflow/catql/eval/sf/trial_0.1_12/received_pcaps > names.list
bash get_header_fields.sh
mv  ~/mnt/anonflow/catql/eval/sf/trial_0.1_12/received_pcaps/*.csv ~/mnt/anonflow/catql/eval/sf/trial_0.1_12/received_csvs/
echo "Done with trial 0.1_12 (4/5)"

python3 create_name_list.py ~/mnt/anonflow/catql/eval/sf/trial_0.9_12/received_pcaps > names.list
bash get_header_fields.sh
mv  ~/mnt/anonflow/catql/eval/sf/trial_0.9_12/received_pcaps/*.csv ~/mnt/anonflow/catql/eval/sf/trial_0.9_12/received_csvs/
echo "Done with trial 0.9_12 (5/5)"

