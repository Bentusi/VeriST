# IEC 61131-3 ST语言编译器（Coq实现）

使用Coq证明助手实现一个经过形式化验证的IEC 61131-3结构化文本（ST）语言编译器。

## 项目概述

本项目将ST源代码编译为字节码，并在虚拟机上执行。参考[STVM项目](https://github.com/Bentusi/STVM)的设计，实现包括：

- **形式化语义**：源语言和字节码的精确语义定义
- **经过验证的编译器**：带有正确性证明的编译器实现
- **类型安全**：完整的类型系统和安全性证明
- **可执行**：可提取为OCaml代码实际运行

## 主要特性

- ✅ 基本数据类型：BOOL, INT, REAL, STRING
- ✅ 控制结构：IF-THEN-ELSE, WHILE, FOR, CASE
- ✅ 函数定义和调用
- ✅ 表达式计算：算术、比较、逻辑运算
- ✅ 变量声明和赋值
- ✅ 编译器正确性证明

## 快速开始

### 依赖要求

- Coq 8.17+ 或更高版本
- OCaml 4.14+ （用于代码提取）
- Make

### 构建项目

```bash
# 编译Coq代码
make

# 运行测试
make test

# 提取OCaml代码
make extract

# 清理生成文件
make clean
```

## 项目结构

```
coq/
├── theories/          # Coq理论文件
│   ├── Common/       # 通用定义
│   ├── Syntax/       # 语法定义
│   ├── Semantics/    # 语义定义
│   ├── Compiler/     # 编译器实现
│   ├── Verification/ # 正确性证明
│   └── Extraction/   # 代码提取
├── examples/         # 示例程序
└── extraction/       # 提取的OCaml代码

详见 [DESIGN.md](./DESIGN.md) 获取完整设计文档。
```

## 示例

一个简单的ST程序：

```st
PROGRAM SimpleCalc
VAR
    a : INT;
    b : INT;
    result : INT;
END_VAR

a := 10;
b := 20;
result := a + b;

END_PROGRAM
```

编译后生成的字节码：

```
0: LOAD_INT 10
1: STORE_VAR "a"
2: LOAD_INT 20
3: STORE_VAR "b"
4: LOAD_VAR "a"
5: LOAD_VAR "b"
6: ADD
7: STORE_VAR "result"
8: HALT
```

## 参考资料

- [STVM项目](https://github.com/Bentusi/STVM) - 参考实现
- [IEC 61131-3标准](https://en.wikipedia.org/wiki/IEC_61131-3) - ST语言标准
- [Software Foundations](https://softwarefoundations.cis.upenn.edu/) - Coq教程
- [CompCert](https://compcert.org/) - 经过验证的C编译器

## 许可证

MIT License

## 贡献

欢迎提交Issue和Pull Request！
