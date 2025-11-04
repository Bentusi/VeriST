(* 斐波那契数列程序
   计算第10个斐波那契数 = 55
*)
PROGRAM Fibonacci
VAR
    n : INT := 10;
    fib_prev : INT := 0;
    fib_curr : INT := 1;
    fib_next : INT;
    counter : INT := 2;
END_VAR

WHILE counter <= n DO
    fib_next := fib_prev + fib_curr;
    fib_prev := fib_curr;
    fib_curr := fib_next;
    counter := counter + 1;
END_WHILE

(* 此时 fib_curr = 55 *)
END_PROGRAM
