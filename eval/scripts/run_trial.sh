#!/bin/bash

mkdir ~/mnt/anonflow/catql/eval/sf/trial_$1/received_pcaps/sliced/
tcpdump -r ~/mnt/anonflow/catql/eval/sf/trial_$1/received_pcaps/campus_10min_$1.pcap -C 1000MB -w ~/mnt/anonflow/catql/eval/sf/trial_$1/received_pcaps/sliced/campus_10min_$1_sliced.pcap
python3 create_name_list.py ~/mnt/anonflow/catql/eval/sf/trial_$1/received_pcaps/sliced > names.list
bash get_header_fields.sh
mv  ~/mnt/anonflow/catql/eval/sf/trial_$1/received_pcaps/sliced/*.csv ~/mnt/anonflow/catql/eval/sf/trial_$1/received_csvs/
echo "Done with trial $1"

