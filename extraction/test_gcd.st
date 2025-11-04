(* 最大公约数程序
   使用欧几里得算法计算 GCD(48, 18) = 6
*)
PROGRAM GCD
VAR
    a : INT := 48;
    b : INT := 18;
    temp : INT;
END_VAR

WHILE b <> 0 DO
    temp := b;
    b := a MOD b;
    a := temp;
END_WHILE

(* 此时 a = 6 *)
END_PROGRAM
