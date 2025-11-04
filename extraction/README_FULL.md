# VeriST 编译器 - 完整工具链

## 概述

VeriST 是一个经过形式化验证的 Structured Text (ST) 编译器，能够将 ST 源代码编译为 STVM 虚拟机字节码。

## 构建

```bash
bash build.sh
```

构建过程包括：
1. 生成词法分析器 (lexer) 和语法分析器 (parser)
2. 编译 Coq 提取的模块
3. 编译 parser 和 lexer
4. 链接生成 veriST 可执行文件

## 使用

### 命令行接口

```bash
./veriST -c <input.st> -o <output.stbc>
```

**选项**:
- `-c <file>`: 指定输入的 ST 源文件
- `-o <file>`: 指定输出的字节码文件 (.stbc)
- `-v, --verbose`: 启用详细输出
- `-h, --help`: 显示帮助信息

### 示例

```bash
# 编译阶乘程序
./veriST -c test_factorial.st -o test_factorial.stbc

# 编译斐波那契程序
./veriST -c test_fibonacci.st -o test_fibonacci.stbc

# 编译 GCD 程序
./veriST -c test_gcd.st -o test_gcd.stbc

# 启用详细输出
./veriST -c test_gcd.st -o test_gcd.stbc -v
```

## ST 语言特性

VeriST 编译器支持以下 ST 语言特性：

### 数据类型
- `INT`: 整数类型
- `BOOL`: 布尔类型

### 变量声明
```pascal
VAR
  a : INT := 48;
  b : INT := 18;
  temp : INT;
END_VAR
```

### 语句
- **赋值**: `variable := expression;`
- **IF-THEN-ELSE**: 条件分支
  ```pascal
  IF condition THEN
    statements
  ELSIF condition THEN
    statements
  ELSE
    statements
  END_IF
  ```
- **WHILE**: 循环
  ```pascal
  WHILE condition DO
    statements
  END_WHILE
  ```
- **FOR**: 计数循环
  ```pascal
  FOR i := 1 TO 10 BY 1 DO
    statements
  END_FOR
  ```

### 表达式
- **常量**: 整数 (`123`), 布尔值 (`TRUE`, `FALSE`)
- **变量**: 标识符
- **算术运算**: `+`, `-`, `*`, `/`, `MOD`
- **比较运算**: `=`, `<>`, `<`, `<=`, `>`, `>=`
- **逻辑运算**: `AND`, `OR`, `NOT`
- **一元运算**: `-` (取负)

### 注释
- 块注释: `(* comment *)`
- 行注释: `// comment`

## 测试文件

### test_factorial.st
计算 5 的阶乘。

**预期结果**: `result = 120`

### test_fibonacci.st
计算第 10 个斐波那契数。

**预期结果**: `fib_curr = 55`

### test_gcd.st
计算 48 和 18 的最大公约数。

**预期结果**: `a = 6`

## 字节码格式

生成的 `.stbc` 文件采用 STVM 兼容的二进制格式：

### 文件头
```
[4 bytes] 指令数量 (小端序)
```

### 指令流
每条指令由操作码和操作数组成：

| 操作码 | 指令 | 操作数 | 说明 |
|--------|------|--------|------|
| 0x01 | LOADINT | 4 bytes (int) | 加载整数常量到栈 |
| 0x02 | LOADBOOL | 1 byte (0/1) | 加载布尔常量到栈 |
| 0x05 | LOADVAR | 1 byte (len) + chars | 加载变量值到栈 |
| 0x06 | STOREVAR | 1 byte (len) + chars | 从栈保存到变量 |
| 0x10 | ADD | - | 加法 |
| 0x11 | SUB | - | 减法 |
| 0x12 | MUL | - | 乘法 |
| 0x13 | DIV | - | 除法 |
| 0x14 | MOD | - | 取模 |
| 0x15 | NEG | - | 取负 |
| 0x20 | EQ | - | 相等比较 |
| 0x21 | NE | - | 不等比较 |
| 0x22 | LT | - | 小于比较 |
| 0x23 | LE | - | 小于等于比较 |
| 0x24 | GT | - | 大于比较 |
| 0x25 | GE | - | 大于等于比较 |
| 0x30 | AND | - | 逻辑与 |
| 0x31 | OR | - | 逻辑或 |
| 0x32 | NOT | - | 逻辑非 |
| 0x40 | JMP | 4 bytes (addr) | 无条件跳转 |
| 0x41 | JZ | 4 bytes (addr) | 为零跳转 |
| 0x42 | JNZ | 4 bytes (addr) | 非零跳转 |
| 0x60 | POP | - | 弹出栈顶 |
| 0xFF | HALT | - | 停机 |

### 示例：test_gcd.stbc

```
00000000  0d 00 00 00              # 13 条指令
00000004  05                       # LOADVAR
00000005  01                       # 长度 = 1
00000006  62                       # 'b'
00000007  01 00 00 00 00           # LOADINT 0
0000000c  21                       # NE
0000000d  41 00 00 00 00           # JZ (跳出循环)
...
```

## 与 STVM 集成

### 1. 克隆并构建 STVM

```bash
git clone https://github.com/Bentusi/STVM.git
cd STVM
make
```

### 2. 复制字节码文件

```bash
cp /path/to/veriST/extraction/*.stbc .
```

### 3. 运行字节码

```bash
./stvm test_factorial.stbc
./stvm test_fibonacci.stbc
./stvm test_gcd.stbc
```

### 4. 验证结果

检查 STVM 输出中的变量最终值：
- `test_factorial.stbc`: `result` 应为 120
- `test_fibonacci.stbc`: `fib_curr` 应为 55
- `test_gcd.stbc`: `a` 应为 6

## 项目结构

```
extraction/
├── veriST                    # 编译器可执行文件
├── build.sh                  # 构建脚本
├── lexer.mll                 # 词法分析器定义
├── parser.mly                # 语法分析器定义
├── veriST.ml                 # 主程序
├── test_*.st                 # ST 源文件
├── test_*.stbc               # 生成的字节码文件
├── *.ml, *.mli               # Coq 提取的模块
└── README.md                 # 本文件
```

## 技术细节

### Coq 提取

编译器核心由 Coq 证明的代码提取：
- `Types.v`: 类型定义
- `AST.v`: 抽象语法树
- `Compiler.v`: 编译器实现
- `VMSemantics.v`: 虚拟机语义

### OCaml 前端

- **lexer.mll**: 使用 ocamllex 生成词法分析器
- **parser.mly**: 使用 ocamlyacc 生成语法分析器
- **veriST.ml**: 命令行接口和字节码生成

### 编译流程

```
ST 源码 → Lexer → Token 流 → Parser → AST → Compiler → 字节码 → .stbc 文件
```

## 已知限制

1. **FOR 循环步长**: 当前仅支持正整数步长
2. **类型系统**: 仅支持 INT 和 BOOL 类型
3. **函数调用**: 尚未完全实现
4. **数组**: 不支持
5. **字符串**: 不支持

## 故障排除

### 构建失败

**问题**: `menhir: 未找到命令`
**解决**: 改用 ocamlyacc (已在 build.sh 中配置)

**问题**: 模块编译顺序错误
**解决**: 确保 Zbool.cmo 在 QArith_base.cmo 之前

### 编译错误

**问题**: `Lexical error: Unexpected character`
**解决**: 检查 ST 源文件语法，确保符合规范

**问题**: `Syntax error at line X`
**解决**: 检查语句结束是否有分号，关键字拼写是否正确

### 运行时错误

**问题**: STVM 无法识别字节码
**解决**: 确保字节码格式正确 (4字节头 + 指令流)

**问题**: 程序结果错误
**解决**: 使用 `-v` 查看编译详情，检查生成的指令数

## 进一步开发

### 短期目标
- [ ] 添加更多测试用例
- [ ] 实现字节码反汇编器
- [ ] 支持更多 ST 语言特性
- [ ] 改进错误报告

### 长期目标
- [ ] 完成所有形式化证明
- [ ] 优化编译器性能
- [ ] 支持 IEC 61131-3 完整规范
- [ ] 与工业 PLC 集成

## 参考

- **IEC 61131-3**: ST 语言标准
- **Coq**: https://coq.inria.fr/
- **STVM**: https://github.com/Bentusi/STVM
- **项目文档**: ../DESIGN.md, ../PHASE5_COMPLETE.md

---

**构建日期**: 2025-11-04  
**版本**: 1.0  
**作者**: VeriST 项目组
