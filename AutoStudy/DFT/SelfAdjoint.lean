/-
  自己随伴演算子の性質

  量子力学における自己随伴（エルミート）演算子の基本的性質を形式化する。
  実数値波動関数の場合、自己随伴性は ⟨ψ|Aφ⟩ = ⟨Aψ|φ⟩ と表される。

  証明する定理:
    - 異なる固有値の固有状態は直交する
    - 自己随伴演算子の行列要素に関する性質
-/
import AutoStudy.DFT.Basic

open MeasureTheory DFT

namespace DFT

/-- 自己随伴（エルミート）演算子: ⟨ψ|Aφ⟩ = ⟨Aψ|φ⟩ -/
def IsSelfAdjoint (A : (ℝ → ℝ) → (ℝ → ℝ)) : Prop :=
  ∀ ψ φ : ℝ → ℝ, innerProduct ψ (A φ) = innerProduct (A ψ) φ

/-- 自己随伴演算子の期待値は対称的:
    ⟨ψ|A|ψ⟩ = ⟨Aψ|ψ⟩ -/
theorem selfAdjoint_expectation_symmetric
    {A : (ℝ → ℝ) → (ℝ → ℝ)} (hsa : IsSelfAdjoint A) (ψ : ℝ → ℝ) :
    expectationValue A ψ = innerProduct (A ψ) ψ :=
  hsa ψ ψ

/-- 自己随伴演算子の行列要素に関する性質:
    ⟨ψ₁|A|ψ₂⟩ = E₂⟨ψ₁|ψ₂⟩ (ψ₂ が固有状態の場合) -/
theorem selfAdjoint_matrix_element_eigenstate
    (A : (ℝ → ℝ) → (ℝ → ℝ)) (ψ₁ ψ₂ : ℝ → ℝ) (E₂ : ℝ)
    (heig₂ : IsEigenstate A ψ₂ E₂) :
    innerProduct ψ₁ (A ψ₂) = E₂ * innerProduct ψ₁ ψ₂ := by
  unfold innerProduct
  have : A ψ₂ = fun x => E₂ * ψ₂ x := heig₂
  simp_rw [this]
  rw [show (fun x => ψ₁ x * (E₂ * ψ₂ x)) = (fun x => E₂ * (ψ₁ x * ψ₂ x)) from by
    ext x; ring]
  rw [integral_const_mul]

/-- 異なる固有値の固有状態は直交する:
    Aψ₁ = E₁ψ₁, Aψ₂ = E₂ψ₂, E₁ ≠ E₂ ⟹ ⟨ψ₁|ψ₂⟩ = 0

    証明:
    自己随伴性より ⟨ψ₁|Aψ₂⟩ = ⟨Aψ₁|ψ₂⟩
    左辺 = E₂⟨ψ₁|ψ₂⟩, 右辺 = E₁⟨ψ₁|ψ₂⟩
    ∴ (E₂ - E₁)⟨ψ₁|ψ₂⟩ = 0
    E₁ ≠ E₂ より ⟨ψ₁|ψ₂⟩ = 0 -/
theorem selfAdjoint_orthogonal_eigenstates
    {A : (ℝ → ℝ) → (ℝ → ℝ)} (hsa : IsSelfAdjoint A)
    (ψ₁ ψ₂ : ℝ → ℝ) (E₁ E₂ : ℝ)
    (heig₁ : IsEigenstate A ψ₁ E₁)
    (heig₂ : IsEigenstate A ψ₂ E₂)
    (hne : E₁ ≠ E₂) :
    innerProduct ψ₁ ψ₂ = 0 := by
  -- 自己随伴性: ⟨ψ₁|Aψ₂⟩ = ⟨Aψ₁|ψ₂⟩
  have hsa_eq := hsa ψ₁ ψ₂
  -- 左辺: ⟨ψ₁|Aψ₂⟩ = E₂⟨ψ₁|ψ₂⟩
  have hleft : innerProduct ψ₁ (A ψ₂) = E₂ * innerProduct ψ₁ ψ₂ :=
    selfAdjoint_matrix_element_eigenstate A ψ₁ ψ₂ E₂ heig₂
  -- 右辺: ⟨Aψ₁|ψ₂⟩ = E₁⟨ψ₁|ψ₂⟩
  have hright : innerProduct (A ψ₁) ψ₂ = E₁ * innerProduct ψ₁ ψ₂ := by
    unfold innerProduct
    have : A ψ₁ = fun x => E₁ * ψ₁ x := heig₁
    simp_rw [this]
    rw [show (fun x => E₁ * ψ₁ x * ψ₂ x) = (fun x => E₁ * (ψ₁ x * ψ₂ x)) from by
      ext x; ring]
    rw [integral_const_mul]
  -- E₂⟨ψ₁|ψ₂⟩ = E₁⟨ψ₁|ψ₂⟩ より (E₂ - E₁)⟨ψ₁|ψ₂⟩ = 0
  rw [hleft, hright] at hsa_eq
  have h_sub : (E₂ - E₁) * innerProduct ψ₁ ψ₂ = 0 := by linarith
  rcases mul_eq_zero.mp h_sub with h | h
  · exact absurd (sub_eq_zero.mp h).symm hne
  · exact h

end DFT
