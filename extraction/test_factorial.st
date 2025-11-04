(* 阶乘计算程序 
   计算 5! = 120
*)
PROGRAM Factorial
VAR
    n : INT := 5;
    result : INT := 1;
    i : INT := 1;
END_VAR

(* 使用循环计算阶乘 *)
WHILE i <= n DO
    result := result * i;
    i := i + 1;
END_WHILE

(* 此时 result = 120 *)
END_PROGRAM
