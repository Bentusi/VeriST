open Bytecode
open Environment
open Types
open Values

type stack = value list

type call_frame = { cf_return_addr : address; cf_base_pointer : int;
                    cf_local_env : env }

type function_info = { fi_name : char list; fi_address : address;
                       fi_param_count : int; fi_return_type : ty }

type function_table = function_info list

type vm_state = { vm_code : code; vm_pc : address; vm_stack : stack;
                  vm_env : env; vm_frames : call_frame list;
                  vm_functions : function_table; vm_halted : bool }

(** val init_vm_state : code -> function_table -> vm_state **)

let init_vm_state c funcs =
  { vm_code = c; vm_pc = 0; vm_stack = []; vm_env = empty; vm_frames = [];
    vm_functions = funcs; vm_halted = false }
