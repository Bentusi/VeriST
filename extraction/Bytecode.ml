open QArith_base

type instr =
| ILoadInt of int
| ILoadReal of coq_Q
| ILoadBool of bool
| ILoadString of char list
| ILoadVar of char list
| IStoreVar of char list
| IAdd
| ISub
| IMul
| IDiv
| IMod
| INeg
| IEq
| INe
| ILt
| ILe
| IGt
| IGe
| IAnd
| IOr
| INot
| IJmp of int
| IJz of int
| IJnz of int
| ICall of int
| IRet
| ILoadParam of int
| IStoreParam of int
| IPop
| IDup
| IHalt
| INop

type code = instr list

type address = int
