# STVM 集成测试报告

## 测试日期
2025年11月7日

## 测试目标
验证 VeriST 编译器生成的字节码能否在 STVM 虚拟机中正常执行

## 测试环境

### VeriST 编译器
- 位置: `/home/wei/coq/extraction/veriST`
- 版本: Phase 5 完成版
- 功能: ST 源码 → STBC 字节码

### STVM 虚拟机  
- 位置: `/home/wei/stvm/stvm`
- 命令: `./stvm -r <file.stbc>`
- 字节码格式版本: 1.0

## 测试过程

### 1. 编译测试程序

使用 VeriST 编译三个测试程序：

```bash
cd /home/wei/coq/extraction

# 阶乘程序
./veriST -c test_factorial.st -o test_factorial.stbc
# ✓ 成功: 13 条指令

# GCD 程序  
./veriST -c test_gcd.st -o test_gcd.stbc
# ✓ 成功: 13 条指令

# 斐波那契程序
./veriST -c test_fibonacci.st -o test_fibonacci.stbc
# ✓ 成功: 17 条指令
```

### 2. 字节码文件格式分析

#### VeriST 生成的字节码结构

```
[STBC 文件头 - 36 字节]
├─ Magic: 0x43425453 ("STBC")
├─ Version: 1.0
├─ Entry point: 0
├─ Global var count: 0
├─ Constant count: 0
├─ Function count: 0
├─ Instruction count: N
├─ Library dep count: 0
└─ Checksum: 0

[指令序列]
├─ ILoadInt n
├─ ILoadVar "varname"
├─ IStoreVar "varname"
├─ IAdd, ISub, IMul, IDiv, IMod
├─ IEq, INe, ILt, ILe, IGt, IGe
├─ IAnd, IOr, INot
├─ IJmp, IJz, IJnz
├─ IPop
└─ IHalt
```

#### STVM 期望的字节码结构

```
[STBC 文件头 - 36 字节]
(同上)

[常量池 - Variable length]
├─ Constant 0: type + value
├─ Constant 1: type + value
└─ ...

[全局变量表 - Variable length]
├─ Variable 0: name + type + init_value
├─ Variable 1: name + type + init_value  
└─ ...

[函数表 - Variable length]
├─ Function 0: metadata + code_offset
├─ Function 1: metadata + code_offset
└─ ...

[指令序列]
├─ PUSH #const_id
├─ LOAD global var_id
├─ STORE global var_id
└─ ...
```

## 关键发现

### 🔴 问题1: 架构差异

**VeriST 设计**:
- 指令直接内嵌常量值 (`ILoadInt 42`)
- 指令直接内嵌变量名 (`ILoadVar "x"`)
- 无常量池和变量表

**STVM 设计**:
- 指令引用常量池索引 (`PUSH #0`)
- 指令引用变量表索引 (`LOAD global 0`)
- 需要常量池和变量表

### 🔴 问题2: 字节码加载失败

```bash
$ cd /home/wei/stvm
$ ./stvm -r /home/wei/coq/extraction/test_factorial.stbc -V
加载字节码文件: /home/wei/coq/extraction/test_factorial.stbc
错误：无法加载字节码文件
```

**原因**: STVM 加载器期望文件头后面有常量池/变量表/函数表等数据区，但 VeriST 生成的文件直接跟指令。

### 🟡 问题3: 指令编码差异

| 指令 | VeriST 编码 | STVM 编码 | 兼容性 |
|------|------------|----------|--------|
| LoadInt | `01 nn nn nn nn` | `PUSH #const_id` | ❌ 不兼容 |
| LoadVar | `05 len name...` | `LOAD global id` | ❌ 不兼容 |
| StoreVar | `06 len name...` | `STORE global id` | ❌ 不兼容 |
| Add | `10` | `ADD` | ✓ 可能兼容 |
| Jmp | `40 addr addr addr addr` | `JMP @addr` | ✓ 可能兼容 |

## 对比分析

### STVM 自生成的 factorial.stbc

```
00000000  53 54 42 43 01 00 00 00  00 13 01 00 00 00 05 06  |STBC............|
                                      ^^^^^ entry=0x00000013
                                            ^^^^^ global_var=1
                                                  ^^^^^ const=5
00000010  00 00 00 01 6e 01 00 00  00 01 06 00 00 00 06 72  |....n..........r|
          ^^^^^ func=1
                ^^ var_name_len=1
                   ^^ 'n'
                      ^^^^^ type=INT
                            ^^^^^ init=1
                                  ^^^^^ next_var_len=6
                                        ^^^^^^^^^ "result"
```

### VeriST 生成的 test_factorial.stbc

```
00000000  53 54 42 43 01 00 00 00  00 00 00 00 00 00 00 00  |STBC............|
                                      ^^^^^ entry=0
                                            ^^^^^ global=0
                                                  ^^^^^ const=0
00000010  00 00 00 00 00 00 00 00  0d 00 00 00 00 00 00 00  |................|
          ^^^^^ func=0
                                   ^^^^^ instr=13
                                             ^^^^^ lib=0
00000020  00 00 00 00 05 01 69 05  01 6e 23 41 00 00 00 00  |......i..n#A....|
          ^^^^^ checksum
                      ^^ ILoadInt (0x01)
                            ^^^^^ value=5
                                  ^^ ILoadVar (0x05)
                                     ^^ len=1
                                        ^^ 'i'
```

## 根本原因分析

### 设计理念差异

1. **VeriST (学术验证导向)**:
   - 简化的字节码格式便于形式化验证
   - 直接编码方式减少间接层级
   - 重点在编译器正确性证明

2. **STVM (工业实现导向)**:
   - 优化的运行时性能（常量池、变量表索引）
   - 支持动态加载和热重载
   - 完整的模块化系统

### 兼容性问题

两种设计都是合理的，但它们**不兼容**：

- **VeriST**: `ILoadInt 42` → 字节序列 `01 2A 00 00 00`
- **STVM**: `PUSH #2` → 字节序列 `1B 02 00 00 00`（其中 2 是常量池索引）

## 解决方案

### 方案1: 修改 VeriST 生成 STVM 兼容字节码 ⭐ 推荐

**优点**:
- 可以使用 STVM 虚拟机执行
- 与现有 STVM 生态集成

**缺点**:
- 需要重新设计字节码生成
- 增加常量池/变量表管理
- 形式化验证变复杂

**工作量**: 中等（2-3天）

**实施步骤**:
1. 实现常量池构建
2. 实现变量表构建
3. 修改指令生成为索引引用
4. 更新字节码序列化
5. 更新形式化证明

### 方案2: 实现简化的 VeriST 虚拟机

**优点**:
- 保持当前简化设计
- 形式化验证更简单
- 完全控制实现

**缺点**:
- 需要实现新的虚拟机
- 不能利用 STVM 生态
- 额外维护负担

**工作量**: 较大（3-5天）

### 方案3: 创建字节码转换工具

**优点**:
- 保持两边独立
- 灵活性高

**缺点**:
- 需要额外工具
- 转换可能有损失
- 增加工具链复杂度

**工作量**: 中等（2-3天）

### 方案4: 混合方案 - 双后端

**优点**:
- 两种格式都支持
- 灵活性最高
- 学术和实用兼顾

**缺点**:
- 代码复杂度增加
- 维护两套生成逻辑

**工作量**: 较大（4-5天）

## 当前状态总结

### ✅ 已完成

1. **词法分析器** (lexer.mll) - 95 行
   - 完整的 ST 关键字识别
   - 运算符和分隔符
   - 注释支持

2. **语法分析器** (parser.mly) - 198 行
   - ST 程序结构解析
   - 表达式和语句解析
   - AST 生成

3. **编译器** (Compiler.v + OCaml 提取)
   - ST → 字节码编译
   - 控制流处理
   - 表达式求值

4. **字节码文件头** (veriST.ml)
   - 正确的 STBC 魔数
   - 版本信息
   - 元数据字段

5. **形式化验证** (Coq 证明)
   - 类型系统
   - 编译器正确性证明
   - 质量位类型支持

### ⏳ 待完成

1. **常量池实现**
   - 提取程序中的常量
   - 生成常量池数据结构
   - 序列化常量池

2. **变量表实现**
   - 提取全局变量声明
   - 分配变量 ID
   - 序列化变量表

3. **指令编码调整**
   - ILoadInt → PUSH #const_id
   - ILoadVar → LOAD global var_id
   - IStoreVar → STORE global var_id

4. **STVM 集成测试**
   - 验证字节码可加载
   - 验证程序执行正确
   - 验证结果准确性

## 测试用例

### test_factorial.st (阶乘)

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

**期望结果**: `result = 120`

### test_gcd.st (最大公约数)

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

**期望结果**: `a = 6`

### test_fibonacci.st (斐波那契)

```pascal
PROGRAM Fibonacci  
VAR
    n : INT := 10;
    fib_prev : INT := 0;
    fib_curr : INT := 1;
    temp : INT;
    i : INT := 2;
END_VAR

WHILE i <= n DO
    temp := fib_curr;
    fib_curr := fib_prev + fib_curr;
    fib_prev := temp;
    i := i + 1;
END_WHILE

END_PROGRAM
```

**期望结果**: `fib_curr = 55`

## 建议

### 短期（本周）

1. **选择方案1**: 修改 VeriST 生成 STVM 兼容字节码
2. **实现常量池**: 提取和序列化常量
3. **实现变量表**: 提取和序列化变量声明
4. **更新指令生成**: 使用索引替代直接值

### 中期（下周）

1. **完整集成测试**: 验证所有测试用例
2. **性能测试**: 对比 STVM 原生编译
3. **文档更新**: 记录字节码格式

### 长期（未来）

1. **扩展功能**: 支持函数调用、数组、结构体
2. **优化**: 常量折叠、死代码消除
3. **工具链**: 反汇编器、调试器

## 参考资料

- STVM 项目: `/home/wei/stvm`
- STVM 字节码头文件: `/home/wei/stvm/src/include/bytecode_io.h`
- STVM 示例: `/home/wei/stvm/examples/`
- VeriST 编译器: `/home/wei/coq/extraction/veriST.ml`
- 字节码定义: `/home/wei/coq/theories/Syntax/Bytecode.v`

## 结论

VeriST 编译器**词法和语法分析已完全按照 STVM 规范实现**，能够正确解析 ST 源代码并生成 AST。

然而，**字节码生成层面存在架构差异**，导致生成的 `.stbc` 文件无法在 STVM 虚拟机中运行。

核心问题是：
- VeriST 使用直接编码（值内嵌在指令中）
- STVM 使用间接编码（指令引用常量池/变量表）

**推荐方案**: 实现常量池和变量表，将 VeriST 字节码格式改为与 STVM 完全兼容。

这需要约 2-3 天工作量，但能够实现与 STVM 生态的完全集成，发挥两个项目的各自优势。
