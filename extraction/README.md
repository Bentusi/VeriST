# VeriST 编译器使用指南

## 项目概述

VeriST 是一个经过 Coq 形式化验证的 IEC 61131-3 ST（结构化文本）编译器。本目录包含从 Coq 提取的 OCaml 代码和编译工具。

## 文件说明

### ST 源代码示例
- `test_factorial.st` - 阶乘计算程序（计算 5! = 120）
- `test_fibonacci.st` - 斐波那契数列程序（计算第10个数 = 55）
- `test_gcd.st` - 最大公约数程序（GCD(48,18) = 6）

### 编译工具
- `stc` - ST 编译器（将 ST 程序编译为字节码）
- `veriST` - 基础测试程序
- `build.sh` - 构建脚本

### 生成的字节码文件
- `factorial.stbc` - 阶乘程序字节码（19条指令）
- `fibonacci.stbc` - 斐波那契程序字节码（25条指令）
- `gcd.stbc` - GCD程序字节码（17条指令）

## 使用步骤

### 1. 编译 ST 程序到字节码

运行编译器生成字节码文件：

```bash
./stc
```

这将读取示例程序的 AST（在 `stc.ml` 中手写构造），并生成对应的 `.stbc` 字节码文件。

输出示例：
```
======================================================
VeriST Compiler - Generating Bytecode Files
======================================================

=== Compiling: Factorial (5!) ===
Generated 19 instructions
✓ Bytecode saved: factorial.stbc (19 instructions)

=== Compiling: Fibonacci (10th number) ===
Generated 25 instructions
✓ Bytecode saved: fibonacci.stbc (25 instructions)

=== Compiling: GCD (48, 18) ===
Generated 17 instructions
✓ Bytecode saved: gcd.stbc (17 instructions)

======================================================
Compilation Complete!
======================================================
```

### 2. 在 STVM 中运行字节码

生成的 `.stbc` 文件采用 STVM 兼容的格式，可以直接在 STVM 虚拟机中运行。

#### 字节码格式规范

```
+------------------+
| Code Length (4B) |  # 32位整数，指令总数
+------------------+
| Instruction 1    |  # 操作码 + 操作数
+------------------+
| Instruction 2    |
+------------------+
| ...              |
+------------------+
```

#### 指令集（部分）

| 操作码 | 指令 | 说明 |
|--------|------|------|
| 0x01 | LOADINT n | 加载整数常量 n 到栈顶 |
| 0x05 | LOADVAR x | 加载变量 x 的值到栈顶 |
| 0x06 | STOREVAR x | 从栈顶弹出值并存储到变量 x |
| 0x10 | ADD | 弹出两个值，相加后压入栈 |
| 0x11 | SUB | 减法 |
| 0x12 | MUL | 乘法 |
| 0x13 | DIV | 除法 |
| 0x14 | MOD | 取模 |
| 0x20 | EQ | 相等比较 |
| 0x21 | NE | 不等比较 |
| 0x22 | LT | 小于比较 |
| 0x23 | LE | 小于等于比较 |
| 0x24 | GT | 大于比较 |
| 0x25 | GE | 大于等于比较 |
| 0x40 | JMP addr | 无条件跳转到地址 addr |
| 0x41 | JZ addr | 条件跳转（栈顶为假时跳转）|
| 0x42 | JNZ addr | 条件跳转（栈顶为真时跳转）|
| 0x60 | POP | 弹出栈顶元素 |
| 0xFF | HALT | 停机 |

### 3. 字节码文件验证

检查字节码文件的十六进制内容：

```bash
hexdump -C factorial.stbc | head -20
```

查看文件大小：

```bash
ls -lh *.stbc
```

## 示例程序说明

### 1. 阶乘程序 (factorial.stbc)

**源代码逻辑：**
```pascal
n := 5;
result := 1;
i := 1;

WHILE i <= n DO
    result := result * i;
    i := i + 1;
END_WHILE

(* result = 120 *)
```

**预期结果：** `result = 120`

### 2. 斐波那契程序 (fibonacci.stbc)

**源代码逻辑：**
```pascal
n := 10;
fib_prev := 0;
fib_curr := 1;
counter := 2;

WHILE counter <= n DO
    fib_next := fib_prev + fib_curr;
    fib_prev := fib_curr;
    fib_curr := fib_next;
    counter := counter + 1;
END_WHILE

(* fib_curr = 55 *)
```

**预期结果：** `fib_curr = 55`

### 3. GCD 程序 (gcd.stbc)

**源代码逻辑：**
```pascal
a := 48;
b := 18;

WHILE b <> 0 DO
    temp := b;
    b := a MOD b;
    a := temp;
END_WHILE

(* a = 6 *)
```

**预期结果：** `a = 6`

## 在 STVM 中测试

如果您有 STVM 虚拟机，可以这样运行：

```bash
# 假设 STVM 可执行文件为 stvm
stvm factorial.stbc
stvm fibonacci.stbc
stvm gcd.stbc
```

## 技术细节

### 编译流程

1. **AST 构造**：在 `stc.ml` 中手动构造抽象语法树
2. **代码生成**：调用 Coq 提取的 `compile_stmt` 函数
3. **字节码输出**：将生成的指令序列写入二进制文件

### 为什么使用手写 AST？

完整的词法/语法分析器（Lexer + Parser）实现较为复杂，需要：
- 词法规则定义（标识符、关键字、运算符等）
- 语法规则定义（BNF 文法）
- 错误处理机制

当前版本采用手写 AST 的方式作为快速原型，未来可以：
1. 使用 OCaml 的 ocamllex + menhir 实现完整解析器
2. 或者集成现有的 ST 解析器库

### 字节码格式选择

采用简单的二进制格式，每条指令包含：
- 1字节操作码
- 可变长度操作数（根据指令类型）

这种格式易于解析，且与 STVM 兼容。

## 扩展计划

- [ ] 实现完整的 ST 词法分析器
- [ ] 实现完整的 ST 语法分析器
- [ ] 支持更多 ST 语言特性（CASE、FOR、函数调用等）
- [ ] 添加字节码优化 pass
- [ ] 实现字节码反汇编工具
- [ ] 集成到 STVM 项目

## 相关资源

- **Coq 源代码**：`../theories/` 目录
- **STVM 项目**：https://github.com/Bentusi/STVM
- **IEC 61131-3 标准**：工业自动化编程语言标准

## 故障排除

### 编译器无法运行

确保所有 `.cmo` 文件已正确编译：

```bash
./build.sh
```

### 字节码文件损坏

重新编译：

```bash
./stc
```

### STVM 无法加载字节码

检查字节码格式是否正确：

```bash
hexdump -C factorial.stbc | head -10
```

确保前4个字节是指令数量（小端序）。

---

**版本**: 1.0  
**日期**: 2025-11-04  
**作者**: VeriST Team
