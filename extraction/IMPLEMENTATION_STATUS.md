# VeriST 字节码生成器 - 实现状态

## ✅ 已完成的功能

### 1. STVM 兼容的字节码格式
- ✅ STBC 1.0 文件格式（36字节头部）
- ✅ 常量池（支持 INT, BOOL, REAL, STRING）
- ✅ 变量表（自动分配索引）
- ✅ 指令序列（4字节/指令）

### 2. 指令映射
- ✅ 24条核心指令已映射到 STVM opcode
- ✅ PUSH (0x00), LOAD (0x03), STORE (0x04)
- ✅ 算术运算：ADD (0x05), SUB (0x06), MUL (0x07), DIV (0x08), MOD (0x09)
- ✅ 比较运算：EQ (0x0E), NE (0x0F), LT (0x10), LE (0x11), GT (0x12), GE (0x13)
- ✅ 逻辑运算：AND (0x14), OR (0x15), NOT (0x16)
- ✅ 控制流：JMP (0x1B), JZ (0x1C), JNZ (0x1D)
- ✅ 其他：POP (0x01), NEG (0x0D), HALT (0x20)

### 3. 变量初始化代码生成
- ✅ 为每个变量生成 PUSH + STORE 指令对
- ✅ 支持默认初始化值（INT=0, BOOL=false, REAL=0.0, STRING=""）
- ✅ 生成 JMP 指令跳过初始化段

### 4. 常量池管理
- ✅ 常量去重机制
- ✅ 常量索引映射
- ✅ 常量池重排（初始化常量优先）
- ✅ 用户代码指令的 operand 重映射

### 5. 程序结构
最终生成的字节码结构：
```
[Init Code]    - 为每个变量生成 PUSH + STORE
[JMP]          - 跳转到用户代码起始点
[User Code]    - 翻译后的用户程序
[HALT]         - 程序终止
```

### 6. 编译测试
- ✅ test_simple.st (1个变量，2条指令) - 编译成功
- ✅ test_factorial.st (3个变量，13条指令) - 编译成功
- ✅ test_gcd.st (3个变量，13条指令) - 编译成功

## ⚠️ 当前问题

### STVM 加载失败
VeriST 生成的字节码无法被 STVM 加载执行。

**症状**：
```
错误：无法加载字节码文件 'xxx.stbc'
```

**可能的原因**：
1. **Checksum 验证** - 当前设置为 0，STVM 可能要求正确的 CRC32
2. **字节序问题** - 虽然理论上都是小端序
3. **Flags 字段** - LOAD/STORE 指令的 flags 可能需要特殊值
4. **文件格式细节** - STVM 加载器可能对格式有严格要求

**已验证**：
- ✅ Magic number 正确：0x43425453 ("STBC")
- ✅ Version 正确：1.0
- ✅ 头部字段数量正确
- ✅ 常量池格式正确（INT 4字节，REAL 8字节）
- ✅ 指令格式正确（opcode + flags + 2字节operand）
- ✅ 指令 opcode 与 STVM 一致（通过 hexdump 对比验证）

## 📋 待实现功能

### 高优先级
1. **CRC32 Checksum 计算**
   - 需要实现标准 CRC32 算法
   - 计算范围：头部之后的所有字节码内容
   - 写入header offset 32-35

2. **STVM 兼容性测试**
   - 调试 STVM 加载失败的真实原因
   - 可能需要查看 STVM 源代码的加载逻辑

### 中优先级
3. **函数支持**
   - 函数定义和调用
   - 参数传递
   - 返回值处理

4. **更多数据类型**
   - REAL 类型的常量和运算
   - STRING 类型的操作

### 低优先级
5. **优化**
   - 常量折叠
   - 死代码消除
   - 指令合并

## 🔍 调试信息

### 字节码对比（test_simple）

**STVM 生成（60字节）：**
```
Header: STBC 1.0, entry=0, vars=1, consts=1, instrs=4
Constants: [42]
Instructions:
  0: PUSH #0
  1: STORE global 0
  2: JMP @3
  3: HALT
```

**VeriST 生成（68字节）：**
```
Header: STBC 1.0, entry=0, vars=1, consts=2, instrs=6
Constants: [0, 42]
Instructions:
  0: PUSH #0        (init)
  1: STORE global 0 (init)
  2: JMP @3         (skip init)
  3: PUSH #1        (user code)
  4: STORE global 0 (user code)
  5: HALT
```

**差异分析**：
- VeriST 多了初始化段（2条指令）
- VeriST 多了一个常量（默认值 0）
- 指令格式和 opcode 完全匹配
- 但 STVM 仍然无法加载

## 📝 下一步计划

1. 实现 CRC32 checksum
2. 如果还不行，需要：
   - 分析 STVM 加载器源代码
   - 或者简化字节码生成，去掉初始化段
   - 或者调试 STVM 看具体在哪里失败

## 文件清单

**核心文件**：
- `bytecode_builder.ml` (300+ 行) - 字节码构建器
- `veriST.ml` (280+ 行) - 命令行编译器
- `build.sh` - 构建脚本

**测试文件**：
- `test_simple.st` - 简单赋值测试
- `test_factorial.st` - 阶乘计算（循环）
- `test_gcd.st` - 最大公约数（循环）

**生成的字节码**：
- `test_simple_final.stbc` (68字节)
- `test_factorial_final.stbc` 
- `test_gcd_final.stbc`
