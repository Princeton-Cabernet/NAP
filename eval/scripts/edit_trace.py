from scapy.all import *
from datetime import datetime
import pickle
import sys

# # Sata: Argument 1 is source path, argument 2 is destination path.


########################################

def edit_trace_file(src_trace_path, dst_trace_path):

    packets = PcapReader(src_trace_path)
    fp = PcapWriter(dst_trace_path, append=False)
    ref_time = 0.0
    start_time = datetime.now()
    print("Starting to process trace. Will update per 10,000 packets processed.", flush=True)

    for i, packet in enumerate(packets):
        try:
            if i == 0:
                ref_time = packet[Ether].time
            else:
                if (i+1)%10000 == 0:
                    time_dur = datetime.now() - start_time
                    total_secs = time_dur.total_seconds()
                    print("\tProcessed {0}K packets in {1}h:{2}m:{3}s time".format(
                            int((i+1)/1000), int(total_secs/3600), str(int(total_secs/60)%60).zfill(2), str(int(total_secs%60)).zfill(2)), flush=True)
                if IP in packet and (packet[IP].proto==6 or packet[IP].proto==17):
                    time_delta = int((packet[Ether].time - ref_time) * (10**6))
                    if time_delta >= 0:
                        # Overwrite ethernet dest. field with frame time
                        frame_time        = time_delta.to_bytes(4, 'big')
                        packet[Ether].dst = (0).to_bytes(2, 'big') + frame_time
                        # Write packet to dst_pcap
                        fp.write(packet)
        except Exception as e:
            print(e)
            raise e
    
    fp.close()

    time_dur = datetime.now() - start_time
    total_secs = time_dur.total_seconds()
    print("Trace processing complete. Processed {0}K packets in {1}h:{2}m:{3}s time".format(
            round((i+1)/1000, 2), int(total_secs/3600), str(int(total_secs/60)%60).zfill(2), str(int(total_secs%60)).zfill(2)), flush=True)

    return

########################################

def main():
    if len(sys.argv) < 3:
        raise Exception("2 arguments expected")
    
    src_trace_path = sys.argv[1]
    dst_trace_path = sys.argv[2]

    edit_trace_file(src_trace_path, dst_trace_path)

########################################

if __name__ == "__main__":
    main()

########################################
