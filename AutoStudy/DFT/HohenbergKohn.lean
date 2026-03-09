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
import AutoStudy.DFT.ExplicitHamiltonian

open MeasureTheory DFT

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

/-- 明示的ハミルトニアンから Hohenberg-Kohn の仮定 hpot1/hpot2 を導く補助定理。

    2 つのハミルトニアンが運動項と相互作用項を共有し、
    外部ポテンシャルだけが異なるとき、任意の波動関数に対する期待値差は
    外部ポテンシャル差の密度積分で表される。 -/
theorem explicit_hamiltonian_expectation_shift
    (H₁ H₂ : ExplicitHamiltonian)
    (hKinetic : H₁.kinetic = H₂.kinetic)
    (hInteraction : H₁.interaction = H₂.interaction)
    (ψ : ℝ → ℝ)
    (hint₁ : H₁.IntegrableState ψ)
    (hint₂ : H₂.IntegrableState ψ) :
    expectationValue H₁.toOperator ψ =
      expectationValue H₂.toOperator ψ + externalEnergy (fun x => H₁.vExt x - H₂.vExt x) ψ := by
  have hdiff := ExplicitHamiltonian.expectation_difference_of_same_core
    H₁ H₂ ψ hKinetic hInteraction hint₁ hint₂
  linarith

/-- 同じ密度を持つ 2 つの波動関数に対して、外部ポテンシャル差の期待値は一致する。 -/
theorem externalEnergy_eq_of_same_density
    (v : ℝ → ℝ) (ψ₁ ψ₂ : ℝ → ℝ)
    (hρ : electronDensity ψ₁ = electronDensity ψ₂) :
    externalEnergy v ψ₁ = externalEnergy v ψ₂ := by
  repeat rw [ExplicitHamiltonian.externalEnergy_eq]
  rw [hρ]

/-- 明示的ハミルトニアン版 Hohenberg-Kohn 第一定理。

    hpot1, hpot2 を直接仮定する代わりに、
    共通の運動項・相互作用項と同一密度から矛盾を導く。 -/
theorem hohenberg_kohn_first_theorem_explicit
    (H₁ H₂ : ExplicitHamiltonian)
    (ψ₁ ψ₂ : ℝ → ℝ)
    (E₁ E₂ : ℝ)
    (hnorm1 : IsNormalized ψ₁)
    (hnorm2 : IsNormalized ψ₂)
    (heig1 : IsEigenstate H₁.toOperator ψ₁ E₁)
    (heig2 : IsEigenstate H₂.toOperator ψ₂ E₂)
    (hvar1 : E₁ < expectationValue H₁.toOperator ψ₂)
    (hvar2 : E₂ < expectationValue H₂.toOperator ψ₁)
    (hKinetic : H₁.kinetic = H₂.kinetic)
    (hInteraction : H₁.interaction = H₂.interaction)
    (hρ : electronDensity ψ₁ = electronDensity ψ₂)
    (hint12₁ : H₁.IntegrableState ψ₂)
    (hint12₂ : H₂.IntegrableState ψ₂)
    (hint21₁ : H₁.IntegrableState ψ₁)
    (hint21₂ : H₂.IntegrableState ψ₁) :
    False := by
  let δV : ℝ := externalEnergy (fun x => H₁.vExt x - H₂.vExt x) ψ₂
  have hpot1 : expectationValue H₁.toOperator ψ₂ = expectationValue H₂.toOperator ψ₂ + δV := by
    dsimp [δV]
    exact explicit_hamiltonian_expectation_shift H₁ H₂ hKinetic hInteraction ψ₂ hint12₁ hint12₂
  have hδeq : externalEnergy (fun x => H₁.vExt x - H₂.vExt x) ψ₁ = δV := by
    dsimp [δV]
    exact externalEnergy_eq_of_same_density
      (fun x => H₁.vExt x - H₂.vExt x) ψ₁ ψ₂ hρ
  have hpot2' : expectationValue H₂.toOperator ψ₁ = expectationValue H₁.toOperator ψ₁ -
      externalEnergy (fun x => H₁.vExt x - H₂.vExt x) ψ₁ := by
    have h := explicit_hamiltonian_expectation_shift H₂ H₁ hKinetic.symm hInteraction.symm ψ₁ hint21₂ hint21₁
    have hneg : externalEnergy (fun x => H₂.vExt x - H₁.vExt x) ψ₁ =
        - externalEnergy (fun x => H₁.vExt x - H₂.vExt x) ψ₁ := by
      repeat rw [ExplicitHamiltonian.externalEnergy_eq]
      have hEq : (fun x => (H₂.vExt x - H₁.vExt x) * electronDensity ψ₁ x) =
          (fun x => -((H₁.vExt x - H₂.vExt x) * electronDensity ψ₁ x)) := by
        ext x
        ring
      rw [hEq, integral_neg]
    rw [hneg] at h
    linarith
  have hpot2 : expectationValue H₂.toOperator ψ₁ = expectationValue H₁.toOperator ψ₁ - δV := by
    rw [hδeq] at hpot2'
    exact hpot2'
  exact hohenberg_kohn_first_theorem H₁.toOperator H₂.toOperator ψ₁ ψ₂ E₁ E₂
    hnorm1 hnorm2 heig1 heig2 hvar1 hvar2 δV hpot1 hpot2
