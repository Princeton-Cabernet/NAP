module Tofino = struct
  type stage_type =
    { mutable stage_table: int
    ; mutable stage_action: int
    ; mutable stage_hash: int
    ; mutable stage_reg: int
    ; mutable stage_block: int }

  let num_stage = 12

  let stage_table = 16

  let stage_action = 31

  let stage_hash = 6

  let stage_reg = 4

  let stage_block = 48

  let gen_stage () =
    {stage_table; stage_action; stage_hash; stage_reg; stage_block}

  let max_hash_per_table = 2

  let extra_block_per_reg = 1

  let max_block_per_reg = 35

  let num_bit_per_block = 1024 * 128

  let num_bit_in_ts = 48

  (* Comment: get this number by the num_slot_log2 of the minimum memory
     size when num_block = 1. *)
  let min_bit_per_hash = 16

  (* Comment: max_16_bit_per_phv is a rather empirical number
     and allocation choice that we have make due to the blackbox logic
     and try-the-best strategy of PHV allocation in the Tofino compiler.
     * Max number of indices, 48, can be covered by 3 32-bit containers. *)
  let max_idx_per_phv = 16
end