# VeriST 编译器快速入门

## 编译器已就绪！

VeriST 编译器已成功构建，可以将 ST 源代码编译为 STVM 字节码。

## 快速使用

### 1. 编译 ST 源文件

```bash
cd extraction

# 编译阶乘程序
./veriST -c test_factorial.st -o test_factorial.stbc

# 编译斐波那契程序
./veriST -c test_fibonacci.st -o test_fibonacci.stbc

# 编译 GCD 程序
./veriST -c test_gcd.st -o test_gcd.stbc
```

### 2. 查看帮助

```bash
./veriST --help
```

### 3. 启用详细输出

```bash
./veriST -c test_gcd.st -o test_gcd.stbc -v
```

输出示例:
```
Reading source file: test_gcd.st
Lexical analysis...
Syntax analysis...
Compiling to bytecode...
Writing bytecode to: test_gcd.stbc
✓ Compilation successful!
  Input:  test_gcd.st
  Output: test_gcd.stbc
  Instructions: 13
```

## 测试程序说明

### test_factorial.st
```pascal
PROGRAM Factorial
VAR
  n : INT := 5;
  result : INT := 1;
  i : INT := 1;
END_VAR

WHILE i <= n DO
  result := result * i;
  i := i + 1;
END_WHILE

END_PROGRAM
```
**预期结果**: result = 120

### test_fibonacci.st
```pascal
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

END_PROGRAM
```
**预期结果**: fib_curr = 55

### test_gcd.st
```pascal
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

END_PROGRAM
```
**预期结果**: a = 6

## 在 STVM 中运行

### 步骤 1: 获取 STVM

```bash
cd ~
git clone https://github.com/Bentusi/STVM.git
cd STVM
make
```

### 步骤 2: 运行字节码

```bash
# 复制字节码文件
cp /home/wei/coq/extraction/test_*.stbc .

# 运行
./stvm test_factorial.stbc
./stvm test_fibonacci.stbc
./stvm test_gcd.stbc
```

### 步骤 3: 验证结果

STVM 会显示程序执行后的变量值。验证：
- factorial: `result` = 120 ✓
- fibonacci: `fib_curr` = 55 ✓
- gcd: `a` = 6 ✓

## 编写自己的 ST 程序

### 示例：计算平方

创建 `square.st`:
```pascal
PROGRAM Square
VAR
  n : INT := 7;
  result : INT;
END_VAR

result := n * n;

END_PROGRAM
```

编译:
```bash
./veriST -c square.st -o square.stbc
```

## 支持的语法

- ✅ 整数 (INT) 和布尔 (BOOL) 类型
- ✅ 变量声明和初始化
- ✅ 赋值语句
- ✅ 算术运算: +, -, *, /, MOD
- ✅ 比较运算: =, <>, <, <=, >, >=
- ✅ 逻辑运算: AND, OR, NOT
- ✅ IF-THEN-ELSIF-ELSE
- ✅ WHILE 循环
- ✅ FOR 循环
- ✅ 注释: (* ... *) 和 //

## 故障排除

### 编译错误

**语法错误**:
```
Syntax error at line 5, column 10
  near: :=
```
→ 检查语句格式，确保有分号

**词法错误**:
```
Lexical error: Unexpected character: @
```
→ 删除不支持的字符

### 字节码问题

**文件太小**:
```bash
ls -lh *.stbc
# 如果文件只有几个字节，可能编译失败
```
→ 使用 `-v` 重新编译查看详情

## 更多信息

- **完整文档**: README_FULL.md
- **项目设计**: ../DESIGN.md
- **Phase 5 报告**: ../PHASE5_COMPLETE.md

## 下一步

1. ✅ 编译器构建完成
2. ✅ 测试用例编译成功
3. ⏳ **当前步骤**: 在 STVM 中测试字节码
4. ⏳ 添加更多测试用例
5. ⏳ 性能优化

---

🎉 **恭喜！您已拥有一个完整的 ST 编译器！**

试试编译自己的 ST 程序吧！
