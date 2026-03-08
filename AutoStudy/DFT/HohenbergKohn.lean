/-
  Hohenberg-Kohn の第一定理

  密度汎関数理論 (DFT) の基礎定理:
  基底状態の電子密度は外部ポテンシャルを (定数の差を除いて) 一意に決定する。

  証明の概要:
    2つの異なるポテンシャル V₁ ≠ V₂ + const が同じ密度 ρ を与えると仮定する。
    変分原理より:
      E₁ < ⟨ψ₂|H₁|ψ₂⟩ = E₂ + ∫(V₁-V₂)ρ dx
      E₂ < ⟨ψ₁|H₂|ψ₁⟩ = E₁ - ∫(V₁-V₂)ρ dx
    辺々加えると E₁ + E₂ < E₁ + E₂ となり矛盾。
-/
import AutoStudy.DFT.Basic

open DFT

/-- Hohenberg-Kohn の第一定理

  異なる外部ポテンシャルが同じ基底状態密度を与えると仮定すると矛盾が生じる。
  これは、基底状態密度が外部ポテンシャルを一意に決定することを意味する。

  仮定の物理的意味:
  - H₁, H₂: 運動エネルギーは共通、外部ポテンシャルのみ異なるハミルトニアン
  - ψ₁, ψ₂: それぞれの基底状態波動関数
  - E₁, E₂: それぞれの基底状態エネルギー
  - hvar1, hvar2: 変分原理の厳密不等式 (基底状態でない波動関数の期待値 > 基底状態エネルギー)
  - δV: ポテンシャル差の密度平均 ∫(V₁-V₂)ρ dx
  - hpot1, hpot2: H₁ と H₂ の差がポテンシャル差のみであること + 密度が同一であること -/
theorem hohenberg_kohn_first_theorem
    (H₁ H₂ : (ℝ → ℝ) → ℝ → ℝ)
    (ψ₁ ψ₂ : ℝ → ℝ)
    (E₁ E₂ : ℝ)
    (hnorm1 : IsNormalized ψ₁)
    (hnorm2 : IsNormalized ψ₂)
    (heig1 : IsEigenstate H₁ ψ₁ E₁)
    (heig2 : IsEigenstate H₂ ψ₂ E₂)
    -- 変分原理 (厳密不等式)
    (hvar1 : E₁ < expectationValue H₁ ψ₂)
    (hvar2 : E₂ < expectationValue H₂ ψ₁)
    -- ハミルトニアン差 = ポテンシャル差、密度同一
    (δV : ℝ)
    (hpot1 : expectationValue H₁ ψ₂ = expectationValue H₂ ψ₂ + δV)
    (hpot2 : expectationValue H₂ ψ₁ = expectationValue H₁ ψ₁ - δV) :
    False := by
  -- Step 1: 固有状態の期待値 = 固有値
  have hE₁ := eigenstate_expectation_eq H₁ ψ₁ E₁ heig1 hnorm1
  have hE₂ := eigenstate_expectation_eq H₂ ψ₂ E₂ heig2 hnorm2
  -- Step 2: 関係式を代入して不等式を整理
  -- E₁ < ⟨ψ₂|H₁|ψ₂⟩ = ⟨ψ₂|H₂|ψ₂⟩ + δV = E₂ + δV
  rw [hpot1, hE₂] at hvar1
  -- E₂ < ⟨ψ₁|H₂|ψ₁⟩ = ⟨ψ₁|H₁|ψ₁⟩ - δV = E₁ - δV
  rw [hpot2, hE₁] at hvar2
  -- Step 3: E₁ < E₂ + δV かつ E₂ < E₁ - δV → E₁ + E₂ < E₁ + E₂ (矛盾)
  linarith
