open Petr4
open P4light
open Prunefunc
module P4Alias = Poulet4.Syntax

let parser_decls =
  [ P4Alias.DeclParser
      ( noinfo
      , to_p4str "EtherIPTCPUDPParser"
      , []
      , [ gen_p4param Directionless (TypTypeName (to_p4str "packet_in")) "pkt"
        ; gen_p4param Out (TypTypeName (to_p4str "header_t")) "hdr" ]
      , []
      , []
      , [ MkParserState
            ( noinfo
            , to_p4str "start"
            , []
            , ParserDirect (noinfo, to_p4str "parse_ethernet") )
        ; MkParserState
            ( noinfo
            , to_p4str "parse_ethernet"
            , [ gen_p4stmt
                  (StatMethodCall
                     ( gen_p4expname ["pkt"; "extract"]
                     , []
                     , [Some (gen_p4expname ["hdr"; "ethernet"])] ) ) ]
            , ParserSelect
                ( noinfo
                , [gen_p4expname ["hdr"; "ethernet"; "ether_type"]]
                , [ MkParserCase
                      ( noinfo
                      , [ gen_p4match
                            (MatchCast (notype, gen_p4expname ["ETHERTYPE_IPV4"])
                            ) ]
                      , to_p4str "parse_ipv4" )
                  ; MkParserCase
                      (noinfo, [gen_p4match MatchDontCare], to_p4str "reject")
                  ] ) )
        ; MkParserState
            ( noinfo
            , to_p4str "parse_ipv4"
            , [ gen_p4stmt
                  (StatMethodCall
                     ( gen_p4expname ["pkt"; "extract"]
                     , []
                     , [Some (gen_p4expname ["hdr"; "ipv4"])] ) ) ]
            , ParserSelect
                ( noinfo
                , [gen_p4expname ["hdr"; "ipv4"; "protocol"]]
                , [ MkParserCase
                      ( noinfo
                      , [ gen_p4match
                            (MatchCast
                               (notype, gen_p4expname ["IP_PROTOCOLS_TCP"]) ) ]
                      , to_p4str "parse_tcp" )
                  ; MkParserCase
                      ( noinfo
                      , [ gen_p4match
                            (MatchCast
                               (notype, gen_p4expname ["IP_PROTOCOLS_UDP"]) ) ]
                      , to_p4str "parse_udp" )
                  ; MkParserCase
                      (noinfo, [gen_p4match MatchDontCare], to_p4str "accept")
                  ] ) )
        ; MkParserState
            ( noinfo
            , to_p4str "parse_tcp"
            , [ gen_p4stmt
                  (StatMethodCall
                     ( gen_p4expname ["pkt"; "extract"]
                     , []
                     , [Some (gen_p4expname ["hdr"; "tcp"])] ) ) ]
            , ParserDirect (noinfo, to_p4str "accept") )
        ; MkParserState
            ( noinfo
            , to_p4str "parse_udp"
            , [ gen_p4stmt
                  (StatMethodCall
                     ( gen_p4expname ["pkt"; "extract"]
                     , []
                     , [Some (gen_p4expname ["hdr"; "udp"])] ) ) ]
            , ParserDirect (noinfo, to_p4str "accept") ) ] )
  ; DeclParser
      ( noinfo
      , to_p4str "SwitchIngressParser"
      , []
      , [ gen_p4param Directionless (TypTypeName (to_p4str "packet_in")) "pkt"
        ; gen_p4param Out (TypTypeName (to_p4str "header_t")) "hdr"
        ; gen_p4param Out (TypTypeName (to_p4str "metadata_t")) "ig_md"
        ; gen_p4param Out
            (TypTypeName (to_p4str "ingress_intrinsic_metadata_t"))
            "ig_intr_md" ]
      , []
      , [ DeclInstantiation
            ( noinfo
            , TypSpecializedType
                (TypTypeName (to_p4str "TofinoIngressParser"), [])
            , []
            , to_p4str "tofino_parser"
            , [] )
        ; DeclInstantiation
            ( noinfo
            , TypSpecializedType
                (TypTypeName (to_p4str "EtherIPTCPUDPParser"), [])
            , []
            , to_p4str "layer4_parser"
            , [] ) ]
      , [ MkParserState
            ( noinfo
            , to_p4str "start"
            , [ gen_p4stmt
                  (gen_p4tbl_call ~args:[["pkt"]; ["hdr"]] "layer4_parser")
              ; gen_p4stmt
                  (gen_p4tbl_call ~args:[["pkt"]; ["ig_intr_md"]]
                     "tofino_parser" ) ]
            , ParserDirect (noinfo, to_p4str "accept") ) ] ) ]

let deparser_decls =
  [ gen_p4ctrl "SwitchIngressDeparser"
      [ (Directionless, TypTypeName (to_p4str "packet_out"), "pkt")
      ; (InOut, TypTypeName (to_p4str "header_t"), "hdr")
      ; (In, TypTypeName (to_p4str "metadata_t"), "ig_md")
      ; ( In
        , TypTypeName (to_p4str "ingress_intrinsic_metadata_for_deparser_t")
        , "ig_intr_dprsr_md" ) ]
      []
      [ StatMethodCall
          (gen_p4expname ["pkt"; "emit"], [], [Some (gen_p4expname ["hdr"])]) ]
  ; DeclParser
      ( noinfo
      , to_p4str "SwitchEgressParser"
      , []
      , [ gen_p4param Directionless (TypTypeName (to_p4str "packet_in")) "pkt"
        ; gen_p4param Out (TypTypeName (to_p4str "header_t")) "hdr"
        ; gen_p4param Out (TypTypeName (to_p4str "metadata_t")) "eg_md"
        ; gen_p4param Out
            (TypTypeName (to_p4str "egress_intrinsic_metadata_t"))
            "eg_intr_md" ]
      , []
      , [ DeclInstantiation
            ( noinfo
            , TypSpecializedType
                (TypTypeName (to_p4str "TofinoEgressParser"), [])
            , []
            , to_p4str "tofino_parser"
            , [] )
        ; DeclInstantiation
            ( noinfo
            , TypSpecializedType
                (TypTypeName (to_p4str "EtherIPTCPUDPParser"), [])
            , []
            , to_p4str "layer4_parser"
            , [] ) ]
      , [ MkParserState
            ( noinfo
            , to_p4str "start"
            , [ gen_p4stmt
                  (gen_p4tbl_call ~args:[["pkt"]; ["hdr"]] "layer4_parser")
              ; gen_p4stmt
                  (gen_p4tbl_call ~args:[["pkt"]; ["eg_intr_md"]]
                     "tofino_parser" ) ]
            , ParserDirect (noinfo, to_p4str "accept") ) ] )
  ; gen_p4ctrl "SwitchEgress"
      [ (InOut, TypTypeName (to_p4str "header_t"), "hdr")
      ; (InOut, TypTypeName (to_p4str "metadata_t"), "eg_md")
      ; (In, TypTypeName (to_p4str "egress_intrinsic_metadata_t"), "eg_intr_md")
      ; ( In
        , TypTypeName (to_p4str "egress_intrinsic_metadata_from_parser_t")
        , "eg_intr_from_prsr" )
      ; ( InOut
        , TypTypeName (to_p4str "egress_intrinsic_metadata_for_deparser_t")
        , "eg_intr_md_for_dprsr" )
      ; ( InOut
        , TypTypeName (to_p4str "egress_intrinsic_metadata_for_output_port_t")
        , "eg_intr_md_for_oport" ) ]
      [] []
  ; gen_p4ctrl "SwitchEgressDeparser"
      [ (Directionless, TypTypeName (to_p4str "packet_out"), "pkt")
      ; (InOut, TypTypeName (to_p4str "header_t"), "hdr")
      ; (In, TypTypeName (to_p4str "metadata_t"), "eg_md")
      ; ( In
        , TypTypeName (to_p4str "egress_intrinsic_metadata_for_deparser_t")
        , "eg_intr_dprsr_md" ) ]
      []
      [ StatMethodCall
          (gen_p4expname ["pkt"; "emit"], [], [Some (gen_p4expname ["hdr"])]) ]
  ; DeclInstantiation
      ( noinfo
      , TypSpecializedType (TypTypeName (to_p4str "Pipeline"), [])
      , [ gen_p4expr
            (ExpNamelessInstantiation
               ( TypSpecializedType
                   (TypTypeName (to_p4str "SwitchIngressParser"), [])
               , [] ) )
        ; gen_p4expr
            (ExpNamelessInstantiation
               ( TypSpecializedType (TypTypeName (to_p4str "SwitchIngress"), [])
               , [] ) )
        ; gen_p4expr
            (ExpNamelessInstantiation
               ( TypSpecializedType
                   (TypTypeName (to_p4str "SwitchIngressDeparser"), [])
               , [] ) )
        ; gen_p4expr
            (ExpNamelessInstantiation
               ( TypSpecializedType
                   (TypTypeName (to_p4str "SwitchEgressParser"), [])
               , [] ) )
        ; gen_p4expr
            (ExpNamelessInstantiation
               ( TypSpecializedType (TypTypeName (to_p4str "SwitchEgress"), [])
               , [] ) )
        ; gen_p4expr
            (ExpNamelessInstantiation
               ( TypSpecializedType
                   (TypTypeName (to_p4str "SwitchEgressDeparser"), [])
               , [] ) ) ]
      , to_p4str "pipe"
      , [] )
  ; DeclInstantiation
      ( noinfo
      , TypSpecializedType (TypTypeName (to_p4str "Switch"), [])
      , [gen_p4expname ["pipe"]]
      , to_p4str "main"
      , [] ) ]
