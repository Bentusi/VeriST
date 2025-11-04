open Bytecode
open Datatypes
open Environment
open List
open Operations
open VM
open Values

(* vm_step : logical inductive *)
(* with constructors : Step_LoadInt Step_LoadReal Step_LoadBool
   Step_LoadString Step_LoadVar Step_StoreVar Step_Add Step_Sub Step_Mul
   Step_Div Step_Mod Step_Neg Step_Eq Step_Ne Step_Lt Step_Le Step_Gt Step_Ge
   Step_And Step_Or Step_Not Step_Jmp Step_Jz_True Step_Jz_False
   Step_Jnz_True Step_Jnz_False Step_Call Step_Ret Step_Pop Step_Dup
   Step_Halt Step_Nop *)


(* vm_multi_step : logical inductive *)
(* with constructors : Multi_refl Multi_step *)


(** val vm_step_exec : vm_state -> vm_state option **)

let vm_step_exec st =
  if st.vm_halted
  then None
  else (match nth_error st.vm_code st.vm_pc with
        | Some instr ->
          (match instr with
           | ILoadInt n ->
             Some { vm_code = st.vm_code; vm_pc = (Stdlib.Int.succ st.vm_pc);
               vm_stack = ((VInt n) :: st.vm_stack); vm_env = st.vm_env;
               vm_frames = st.vm_frames; vm_functions = st.vm_functions;
               vm_halted = false }
           | ILoadReal r ->
             Some { vm_code = st.vm_code; vm_pc = (Stdlib.Int.succ st.vm_pc);
               vm_stack = ((VReal r) :: st.vm_stack); vm_env = st.vm_env;
               vm_frames = st.vm_frames; vm_functions = st.vm_functions;
               vm_halted = false }
           | ILoadBool b ->
             Some { vm_code = st.vm_code; vm_pc = (Stdlib.Int.succ st.vm_pc);
               vm_stack = ((VBool b) :: st.vm_stack); vm_env = st.vm_env;
               vm_frames = st.vm_frames; vm_functions = st.vm_functions;
               vm_halted = false }
           | ILoadString s ->
             Some { vm_code = st.vm_code; vm_pc = (Stdlib.Int.succ st.vm_pc);
               vm_stack = ((VString s) :: st.vm_stack); vm_env = st.vm_env;
               vm_frames = st.vm_frames; vm_functions = st.vm_functions;
               vm_halted = false }
           | ILoadVar x ->
             (match lookup st.vm_env x with
              | Some v ->
                Some { vm_code = st.vm_code; vm_pc = (Stdlib.Int.succ
                  st.vm_pc); vm_stack = (v :: st.vm_stack); vm_env =
                  st.vm_env; vm_frames = st.vm_frames; vm_functions =
                  st.vm_functions; vm_halted = false }
              | None -> None)
           | IStoreVar x ->
             (match st.vm_stack with
              | [] -> None
              | v :: stk' ->
                Some { vm_code = st.vm_code; vm_pc = (Stdlib.Int.succ
                  st.vm_pc); vm_stack = stk'; vm_env =
                  (update st.vm_env x v); vm_frames = st.vm_frames;
                  vm_functions = st.vm_functions; vm_halted = false })
           | IAdd ->
             (match st.vm_stack with
              | [] -> None
              | v2 :: l ->
                (match l with
                 | [] -> None
                 | v1 :: stk' ->
                   (match eval_add v1 v2 with
                    | Some v ->
                      Some { vm_code = st.vm_code; vm_pc = (Stdlib.Int.succ
                        st.vm_pc); vm_stack = (v :: stk'); vm_env =
                        st.vm_env; vm_frames = st.vm_frames; vm_functions =
                        st.vm_functions; vm_halted = false }
                    | None -> None)))
           | ISub ->
             (match st.vm_stack with
              | [] -> None
              | v2 :: l ->
                (match l with
                 | [] -> None
                 | v1 :: stk' ->
                   (match eval_sub v1 v2 with
                    | Some v ->
                      Some { vm_code = st.vm_code; vm_pc = (Stdlib.Int.succ
                        st.vm_pc); vm_stack = (v :: stk'); vm_env =
                        st.vm_env; vm_frames = st.vm_frames; vm_functions =
                        st.vm_functions; vm_halted = false }
                    | None -> None)))
           | IMul ->
             (match st.vm_stack with
              | [] -> None
              | v2 :: l ->
                (match l with
                 | [] -> None
                 | v1 :: stk' ->
                   (match eval_mul v1 v2 with
                    | Some v ->
                      Some { vm_code = st.vm_code; vm_pc = (Stdlib.Int.succ
                        st.vm_pc); vm_stack = (v :: stk'); vm_env =
                        st.vm_env; vm_frames = st.vm_frames; vm_functions =
                        st.vm_functions; vm_halted = false }
                    | None -> None)))
           | IDiv ->
             (match st.vm_stack with
              | [] -> None
              | v2 :: l ->
                (match l with
                 | [] -> None
                 | v1 :: stk' ->
                   (match eval_div v1 v2 with
                    | Some v ->
                      Some { vm_code = st.vm_code; vm_pc = (Stdlib.Int.succ
                        st.vm_pc); vm_stack = (v :: stk'); vm_env =
                        st.vm_env; vm_frames = st.vm_frames; vm_functions =
                        st.vm_functions; vm_halted = false }
                    | None -> None)))
           | IMod ->
             (match st.vm_stack with
              | [] -> None
              | v2 :: l ->
                (match l with
                 | [] -> None
                 | v1 :: stk' ->
                   (match eval_mod v1 v2 with
                    | Some v ->
                      Some { vm_code = st.vm_code; vm_pc = (Stdlib.Int.succ
                        st.vm_pc); vm_stack = (v :: stk'); vm_env =
                        st.vm_env; vm_frames = st.vm_frames; vm_functions =
                        st.vm_functions; vm_halted = false }
                    | None -> None)))
           | INeg ->
             (match st.vm_stack with
              | [] -> None
              | v1 :: stk' ->
                (match eval_neg v1 with
                 | Some v ->
                   Some { vm_code = st.vm_code; vm_pc = (Stdlib.Int.succ
                     st.vm_pc); vm_stack = (v :: stk'); vm_env = st.vm_env;
                     vm_frames = st.vm_frames; vm_functions =
                     st.vm_functions; vm_halted = false }
                 | None -> None))
           | IEq ->
             (match st.vm_stack with
              | [] -> None
              | v2 :: l ->
                (match l with
                 | [] -> None
                 | v1 :: stk' ->
                   (match eval_eq v1 v2 with
                    | Some v ->
                      Some { vm_code = st.vm_code; vm_pc = (Stdlib.Int.succ
                        st.vm_pc); vm_stack = (v :: stk'); vm_env =
                        st.vm_env; vm_frames = st.vm_frames; vm_functions =
                        st.vm_functions; vm_halted = false }
                    | None -> None)))
           | INe ->
             (match st.vm_stack with
              | [] -> None
              | v2 :: l ->
                (match l with
                 | [] -> None
                 | v1 :: stk' ->
                   (match eval_ne v1 v2 with
                    | Some v ->
                      Some { vm_code = st.vm_code; vm_pc = (Stdlib.Int.succ
                        st.vm_pc); vm_stack = (v :: stk'); vm_env =
                        st.vm_env; vm_frames = st.vm_frames; vm_functions =
                        st.vm_functions; vm_halted = false }
                    | None -> None)))
           | ILt ->
             (match st.vm_stack with
              | [] -> None
              | v2 :: l ->
                (match l with
                 | [] -> None
                 | v1 :: stk' ->
                   (match eval_lt v1 v2 with
                    | Some v ->
                      Some { vm_code = st.vm_code; vm_pc = (Stdlib.Int.succ
                        st.vm_pc); vm_stack = (v :: stk'); vm_env =
                        st.vm_env; vm_frames = st.vm_frames; vm_functions =
                        st.vm_functions; vm_halted = false }
                    | None -> None)))
           | ILe ->
             (match st.vm_stack with
              | [] -> None
              | v2 :: l ->
                (match l with
                 | [] -> None
                 | v1 :: stk' ->
                   (match eval_le v1 v2 with
                    | Some v ->
                      Some { vm_code = st.vm_code; vm_pc = (Stdlib.Int.succ
                        st.vm_pc); vm_stack = (v :: stk'); vm_env =
                        st.vm_env; vm_frames = st.vm_frames; vm_functions =
                        st.vm_functions; vm_halted = false }
                    | None -> None)))
           | IGt ->
             (match st.vm_stack with
              | [] -> None
              | v2 :: l ->
                (match l with
                 | [] -> None
                 | v1 :: stk' ->
                   (match eval_gt v1 v2 with
                    | Some v ->
                      Some { vm_code = st.vm_code; vm_pc = (Stdlib.Int.succ
                        st.vm_pc); vm_stack = (v :: stk'); vm_env =
                        st.vm_env; vm_frames = st.vm_frames; vm_functions =
                        st.vm_functions; vm_halted = false }
                    | None -> None)))
           | IGe ->
             (match st.vm_stack with
              | [] -> None
              | v2 :: l ->
                (match l with
                 | [] -> None
                 | v1 :: stk' ->
                   (match eval_ge v1 v2 with
                    | Some v ->
                      Some { vm_code = st.vm_code; vm_pc = (Stdlib.Int.succ
                        st.vm_pc); vm_stack = (v :: stk'); vm_env =
                        st.vm_env; vm_frames = st.vm_frames; vm_functions =
                        st.vm_functions; vm_halted = false }
                    | None -> None)))
           | IAnd ->
             (match st.vm_stack with
              | [] -> None
              | v :: l ->
                (match v with
                 | VBool b2 ->
                   (match l with
                    | [] -> None
                    | v0 :: stk' ->
                      (match v0 with
                       | VBool b1 ->
                         Some { vm_code = st.vm_code; vm_pc =
                           (Stdlib.Int.succ st.vm_pc); vm_stack = ((VBool
                           ((&&) b1 b2)) :: stk'); vm_env = st.vm_env;
                           vm_frames = st.vm_frames; vm_functions =
                           st.vm_functions; vm_halted = false }
                       | _ -> None))
                 | _ -> None))
           | IOr ->
             (match st.vm_stack with
              | [] -> None
              | v :: l ->
                (match v with
                 | VBool b2 ->
                   (match l with
                    | [] -> None
                    | v0 :: stk' ->
                      (match v0 with
                       | VBool b1 ->
                         Some { vm_code = st.vm_code; vm_pc =
                           (Stdlib.Int.succ st.vm_pc); vm_stack = ((VBool
                           ((||) b1 b2)) :: stk'); vm_env = st.vm_env;
                           vm_frames = st.vm_frames; vm_functions =
                           st.vm_functions; vm_halted = false }
                       | _ -> None))
                 | _ -> None))
           | INot ->
             (match st.vm_stack with
              | [] -> None
              | v :: stk' ->
                (match v with
                 | VBool b ->
                   Some { vm_code = st.vm_code; vm_pc = (Stdlib.Int.succ
                     st.vm_pc); vm_stack = ((VBool (negb b)) :: stk');
                     vm_env = st.vm_env; vm_frames = st.vm_frames;
                     vm_functions = st.vm_functions; vm_halted = false }
                 | _ -> None))
           | IJmp addr ->
             Some { vm_code = st.vm_code; vm_pc = addr; vm_stack =
               st.vm_stack; vm_env = st.vm_env; vm_frames = st.vm_frames;
               vm_functions = st.vm_functions; vm_halted = false }
           | IJz addr ->
             (match st.vm_stack with
              | [] -> None
              | v :: stk' ->
                (match v with
                 | VBool b ->
                   if b
                   then Some { vm_code = st.vm_code; vm_pc = (Stdlib.Int.succ
                          st.vm_pc); vm_stack = stk'; vm_env = st.vm_env;
                          vm_frames = st.vm_frames; vm_functions =
                          st.vm_functions; vm_halted = false }
                   else Some { vm_code = st.vm_code; vm_pc = addr; vm_stack =
                          stk'; vm_env = st.vm_env; vm_frames = st.vm_frames;
                          vm_functions = st.vm_functions; vm_halted = false }
                 | _ -> None))
           | IJnz addr ->
             (match st.vm_stack with
              | [] -> None
              | v :: stk' ->
                (match v with
                 | VBool b ->
                   if b
                   then Some { vm_code = st.vm_code; vm_pc = addr; vm_stack =
                          stk'; vm_env = st.vm_env; vm_frames = st.vm_frames;
                          vm_functions = st.vm_functions; vm_halted = false }
                   else Some { vm_code = st.vm_code; vm_pc = (Stdlib.Int.succ
                          st.vm_pc); vm_stack = stk'; vm_env = st.vm_env;
                          vm_frames = st.vm_frames; vm_functions =
                          st.vm_functions; vm_halted = false }
                 | _ -> None))
           | IPop ->
             (match st.vm_stack with
              | [] -> None
              | _ :: stk' ->
                Some { vm_code = st.vm_code; vm_pc = (Stdlib.Int.succ
                  st.vm_pc); vm_stack = stk'; vm_env = st.vm_env; vm_frames =
                  st.vm_frames; vm_functions = st.vm_functions; vm_halted =
                  false })
           | IDup ->
             (match st.vm_stack with
              | [] -> None
              | v :: _ ->
                Some { vm_code = st.vm_code; vm_pc = (Stdlib.Int.succ
                  st.vm_pc); vm_stack = (v :: st.vm_stack); vm_env =
                  st.vm_env; vm_frames = st.vm_frames; vm_functions =
                  st.vm_functions; vm_halted = false })
           | IHalt ->
             Some { vm_code = st.vm_code; vm_pc = st.vm_pc; vm_stack =
               st.vm_stack; vm_env = st.vm_env; vm_frames = st.vm_frames;
               vm_functions = st.vm_functions; vm_halted = true }
           | INop ->
             Some { vm_code = st.vm_code; vm_pc = (Stdlib.Int.succ st.vm_pc);
               vm_stack = st.vm_stack; vm_env = st.vm_env; vm_frames =
               st.vm_frames; vm_functions = st.vm_functions; vm_halted =
               false }
           | _ -> None)
        | None -> None)

(** val run_vm : int -> vm_state -> vm_state **)

let rec run_vm fuel st =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> st)
    (fun fuel' ->
    if st.vm_halted
    then st
    else (match vm_step_exec st with
          | Some st' -> run_vm fuel' st'
          | None -> st))
    fuel
