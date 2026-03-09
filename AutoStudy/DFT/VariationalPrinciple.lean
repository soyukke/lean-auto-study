/-
  変分原理

  量子力学の変分原理を形式化する。
  任意の正規化された試行波動関数 φ に対して、
  ⟨φ|H|φ⟩ ≥ E₀ (基底状態エネルギー)

  証明可能な定理:
    - 基底状態の期待値 = 基底状態エネルギー
    - 基底状態は期待値を最小化する
    - 非縮退基底状態に対する厳密不等式
-/
import AutoStudy.DFT.Basic

open DFT

namespace DFT

/-- 基底状態: ハミルトニアン H の固有状態 ψ₀ で、
    変分原理 (任意の正規化波動関数に対して期待値が最小) を満たすもの。 -/
structure GroundState where
  /-- ハミルトニアン演算子 -/
  H : (ℝ → ℝ) → ℝ → ℝ
  /-- 基底状態波動関数 -/
  ψ₀ : ℝ → ℝ
  /-- 基底状態エネルギー -/
  E₀ : ℝ
  /-- ψ₀ は H の固有状態: Hψ₀ = E₀ψ₀ -/
  eigenstate : IsEigenstate H ψ₀ E₀
  /-- ψ₀ は正規化されている: ⟨ψ₀|ψ₀⟩ = 1 -/
  normalized : IsNormalized ψ₀
  /-- 変分原理: ∀ normalized φ, ⟨φ|H|φ⟩ ≥ E₀ -/
  variational : ∀ φ : ℝ → ℝ, IsNormalized φ → E₀ ≤ expectationValue H φ

namespace GroundState

variable (gs : GroundState)

/-- 基底状態の期待値は基底状態エネルギーに等しい: ⟨ψ₀|H|ψ₀⟩ = E₀ -/
theorem expectation_eq : expectationValue gs.H gs.ψ₀ = gs.E₀ :=
  eigenstate_expectation_eq gs.H gs.ψ₀ gs.E₀ gs.eigenstate gs.normalized

/-- 基底状態は期待値を最小化する: ∀ φ, ⟨ψ₀|H|ψ₀⟩ ≤ ⟨φ|H|φ⟩ -/
theorem minimizes_energy (φ : ℝ → ℝ) (hφ : IsNormalized φ) :
    expectationValue gs.H gs.ψ₀ ≤ expectationValue gs.H φ := by
  rw [gs.expectation_eq]
  exact gs.variational φ hφ

/-- 変分原理の厳密不等式 (非縮退基底状態):
    φ ≠ ψ₀ ならば ⟨φ|H|φ⟩ > E₀ -/
theorem strict_variational
    (hnd : ∀ φ, IsNormalized φ → expectationValue gs.H φ = gs.E₀ → φ = gs.ψ₀)
    (φ : ℝ → ℝ) (hφ : IsNormalized φ) (hne : φ ≠ gs.ψ₀) :
    gs.E₀ < expectationValue gs.H φ := by
  rcases lt_or_eq_of_le (gs.variational φ hφ) with h | h
  · exact h
  · exact absurd (hnd φ hφ h.symm) hne

/-- 2つの基底状態が存在すれば、エネルギーは等しい -/
theorem unique_ground_energy (gs₁ gs₂ : GroundState) (hH : gs₁.H = gs₂.H) :
    gs₁.E₀ = gs₂.E₀ := by
  apply le_antisymm
  · have h := gs₁.variational gs₂.ψ₀ gs₂.normalized
    rw [hH, gs₂.expectation_eq] at h
    exact h
  · have h := gs₂.variational gs₁.ψ₀ gs₁.normalized
    rw [← hH, gs₁.expectation_eq] at h
    exact h

/-- Rayleigh-Ritz 型の性質: 基底状態エネルギーは正規化状態全体での下界。 -/
theorem rayleigh_ritz_lower_bound (φ : ℝ → ℝ) (hφ : IsNormalized φ) :
    gs.E₀ ≤ expectationValue gs.H φ :=
  gs.variational φ hφ

/-- Rayleigh 商が基底状態で最小値を取ることの言い換え。 -/
theorem rayleigh_ritz_minimizer (φ : ℝ → ℝ) (hφ : IsNormalized φ) :
    expectationValue gs.H gs.ψ₀ = gs.E₀ ∧
    expectationValue gs.H gs.ψ₀ ≤ expectationValue gs.H φ := by
  constructor
  · exact gs.expectation_eq
  · exact gs.minimizes_energy φ hφ

end GroundState

end DFT
