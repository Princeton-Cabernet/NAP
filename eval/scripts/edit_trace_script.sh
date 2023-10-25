#!/bin/bash

for i in {147..216}
do 
    python3 edit_trace.py ~/mnt/anonflow/dynamids_data/pcaps/08_19_2020_T12-15/capture.pcap$i ~/mnt/anonflow/joon/ctrlapp/pcaps/edited_trace/capture_edit.pcap$i
done

