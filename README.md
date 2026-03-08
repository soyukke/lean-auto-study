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
- **交換相関汎関数** (`DFT/ExchangeCorrelation.lean`) — XCFunctional構造体、局所・半局所汎関数の定義
- **座標スケーリング** (`DFT/Scaling.lean`) — 密度のスケーリング変換、合成則、スケーリング条件
- **汎関数微分** (`DFT/FunctionalDerivative.lean`) — Gateaux微分としての定義、線形汎関数の微分、加法性・スカラー倍
- **厳密条件** (`DFT/ExactConstraints.lean`) — 非正性、Lieb-Oxford限界、自己相互作用補正、均一密度極限
- **和則** (`DFT/ExactConstraints/SumRules.lean`) — 交換・相関ホールの和則、ホールの非正性、交換相関ホールの和則定理
- **漸近的性質** (`DFT/ExactConstraints/Asymptotic.lean`) — 長距離挙動 v_xc→-1/r、高密度・低密度極限、局所ポテンシャルの漸近的限界（LDA/GGAが正しい漸近挙動を持てない証明）、漸近補正付きポテンシャル
- **サイズ整合性** (`DFT/ExactConstraints/SizeConsistency.lean`) — サイズ整合性、局所汎関数のサイズ整合性証明、並進不変性、凸性、正の同次性
- **LDA** (`DFT/LDA.lean`) — 局所密度近似の定義、交換・相関の非正性証明、Lieb-Oxford限界との整合性
- **GGA** (`DFT/GGA.lean`) — 一般化勾配近似の定義、LDA帰着、enhancement factor の有界性
- **条件充足比較表** (`DFT/Functionals/Comparison.lean`) — LDA/GGAの厳密条件充足の型レベル表現、サイズ整合性証明、改善ターゲットの明示

全ての定理は `sorry` なしで完全に証明済み。

## ビルド

```bash
# Nix flake 環境
nix develop --command lake build
```

## 依存

- Lean 4 (v4.29.0-rc4)
- Mathlib (v4.29.0-rc4)
