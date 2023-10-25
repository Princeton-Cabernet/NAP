#!/bin/bash


for i in "0.5_6" "0.5_9" "0.5_12" "0.1_12" "0.9_12"
do
    # Trial 0.5 6 stages
    mkdir script_trial_$i
    cp create_name_list.py  ./script_trial_$i
    cp get_header_fields.sh ./script_trial_$i
    cp run_trial.sh ./script_trial_$i
    cd ./script_trial_$i
    bash run_trial.sh $i &
    cd ..
done 

