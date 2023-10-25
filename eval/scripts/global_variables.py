import os

REPO_CURRENT_PATH = os.path.dirname(os.path.realpath(__file__))
REPO_PATH = os.path.realpath(os.path.join(REPO_CURRENT_PATH, '..'))

# Please DO NOT change the names of features.
# They are used to infer the alphabetical order of features in the machine learning model.
all_header_titles = [
                    # IP
                    'version',
                    'ip_hdr_len',

                    # ToS and DS refer to the same field
                    # Reference: https://en.wikipedia.org/wiki/Type_of_service
                    # 8-bit DS/ToS field
                    'ip_dsfield',
                    # Split ToS (Type of Service)
                    # [3, 1, 1, 1, 1, 1(unused bit)]
                    'tos_precedence',
                    'tos_delay',
                    'tos_throughput',
                    'tos_reliability',
                    'tos_cost',
                    # Another way to split DS (Differentiated Services)
                    # [6, 2]
                    'ip_dsfield_dscp',
                    'ip_dsfield_ecn',

                    'ip_len',
                    'ip_id',

                    # rb (reserved bit) and sf (security bit) refer to the same field.
                    # Reserved bit should normally be 0; when set to 1, can be used to tag malicious packets
                    # Reference: https://tools.ietf.org/html/rfc3514
                    # [1, 1, 1]
                    'flags_rb',
                    'flags_sf',
                    'flags_df',
                    'flags_mf',
                    
                    'frag_offset',
                    'ip_fragment',    # This does not look like a header field; it seems like some stateful feature collected by tshark.
                    'fragment_count', # This does not look like a header field; it seems like some stateful feature collected by tshark.
                    'ttl',
                    'protocol',
                    'src_ip', #'src_ip_1', 'src_ip_2', 'src_ip_3',
                    'dst_ip',# 'dst_ip_1', 'dst_ip_2', 'dst_ip_3',
                    'ip_src_rt',      # This does not look like a header field; it seems like live traffic info collected by tshark.
                    'ip_opt_flag',
                    'ip_opt_type',
                    'ip_opt_type_number',
                    'ip_opt_type_class',

                    # TCP & UDP
                    'src_port',
                    'dst_port',
                    'tcp_seq',
                    'tcp_ack',

                    # I don't know what this field is. 
                    # There should be 3 reserved bits in the TCP header, but this field is a boolean in tshark.
                    # The BigQuery table has values Null or 0. 
                    'tcp_flags_res',

                    # All the other flags
                    'tcp_flags_ns',
                    'tcp_flags_cwr',
                    'tcp_flags_ecn',

                    'tcp_flags_urg',
                    'tcp_flags_ack',
                    'tcp_hdr_len',

                    'tcp_flags_push',
                    'tcp_flags_reset',
                    'tcp_flags_syn',
                    'tcp_flags_fin',

                    'tcp_window_size',
                    'tcp_urgent_pointer',
                    'tcp_option_len',

                    # Length information
                    'length',      # frame length
                    'tcp_len',     # segment length

                    'time_stamp',
                    # 's_id'
                    'src_mac',
                    'dst_mac'
                     ]
