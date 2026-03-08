# AutoStudy

Lean 4 + Mathlib による数学・物理の形式化プロジェクト。

## 内容

### 数学
- **√2 の無理数性** (`Sqrt2Irrational.lean`) — Mathlib の `irrational_sqrt_two` を利用した証明と、無限降下法による直接証明

### 古典力学
- **1次元エネルギー保存則** (`EnergyConservation.lean`) — ニュートンの運動方程式のもとで全エネルギー dE/dt = 0 を証明

### 密度汎関数理論 (DFT)
第一原理計算の数学的基礎を Lean 4 で形式化。

- **基礎定義** (`DFT/Basic.lean`) — 内積、期待値、固有状態、電子密度
- **Hohenberg-Kohn 第一定理** (`DFT/HohenbergKohn.lean`) — 異なる外部ポテンシャルが同じ基底状態密度を与えないことの証明
- **変分原理** (`DFT/VariationalPrinciple.lean`) — 基底状態が期待値を最小化、非縮退基底状態の厳密不等式、基底状態エネルギーの一意性
- **Hohenberg-Kohn 第二定理** (`DFT/HohenbergKohnSecond.lean`) — エネルギー汎関数の最小化、v-表現可能密度
- **Kohn-Sham 方程式** (`DFT/KohnSham.lean`) — KS系の定式化、密度の非負性と粒子数保存、有効ポテンシャル分解、自己無撞着条件
- **自己随伴演算子** (`DFT/SelfAdjoint.lean`) — 自己随伴性の定義、異なる固有値の固有状態の直交性、行列要素の性質
- **Hellmann-Feynman 定理** (`DFT/HellmannFeynman.lean`) — 摂動ハミルトニアンの期待値によるエネルギー変化、固有値摂動関係

全ての定理は `sorry` なしで完全に証明済み。

## ビルド

```bash
# Nix flake 環境
nix develop --command lake build
```

## 依存

- Lean 4 (v4.29.0-rc4)
- Mathlib (v4.29.0-rc4)
