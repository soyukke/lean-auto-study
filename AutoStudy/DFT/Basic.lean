/-
  密度汎関数理論 (DFT) の基礎定義

  第一原理計算の数学的基礎を形式化する。
  簡略化のため実数値1粒子波動関数を使用する。
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

noncomputable section

open MeasureTheory

namespace DFT

/-- 波動関数の内積 ⟨ψ|φ⟩ = ∫ ψ(x) · φ(x) dx -/
def innerProduct (ψ φ : ℝ → ℝ) : ℝ :=
  ∫ x, ψ x * φ x

/-- 正規化条件 ⟨ψ|ψ⟩ = 1 -/
def IsNormalized (ψ : ℝ → ℝ) : Prop :=
  innerProduct ψ ψ = 1

/-- 演算子の期待値 ⟨ψ|A|ψ⟩ = ∫ ψ(x) · (Aψ)(x) dx -/
def expectationValue (A : (ℝ → ℝ) → (ℝ → ℝ)) (ψ : ℝ → ℝ) : ℝ :=
  ∫ x, ψ x * A ψ x

/-- 固有状態条件: Aψ = Eψ -/
def IsEigenstate (A : (ℝ → ℝ) → (ℝ → ℝ)) (ψ : ℝ → ℝ) (E : ℝ) : Prop :=
  A ψ = fun x => E * ψ x

/-- 電子密度 ρ(x) = ψ(x) · ψ(x) -/
def electronDensity (ψ : ℝ → ℝ) : ℝ → ℝ := fun x => ψ x * ψ x

/-- 電子密度は非負 -/
theorem electronDensity_nonneg (ψ : ℝ → ℝ) (x : ℝ) :
    0 ≤ electronDensity ψ x :=
  mul_self_nonneg (ψ x)

/-- 正規化波動関数の密度の積分は 1 -/
theorem electronDensity_integral_one (ψ : ℝ → ℝ)
    (hnorm : IsNormalized ψ) :
    ∫ x, electronDensity ψ x = 1 := by
  change innerProduct ψ ψ = 1
  exact hnorm

/-- 固有状態の期待値は固有値に等しい:
    Aψ = Eψ かつ ⟨ψ|ψ⟩ = 1 ならば ⟨ψ|A|ψ⟩ = E -/
theorem eigenstate_expectation_eq
    (A : (ℝ → ℝ) → (ℝ → ℝ)) (ψ : ℝ → ℝ) (E : ℝ)
    (heig : IsEigenstate A ψ E)
    (hnorm : IsNormalized ψ) :
    expectationValue A ψ = E := by
  -- 被積分関数を整理: ψ(x)·(Aψ)(x) = E·ψ(x)·ψ(x)
  have key : ∀ x, ψ x * A ψ x = E * (ψ x * ψ x) := by
    intro x
    have := congr_fun heig x
    rw [this]
    ring
  unfold expectationValue
  simp_rw [key]
  rw [integral_const_mul]
  have : innerProduct ψ ψ = 1 := hnorm
  change E * ∫ x, ψ x * ψ x = E
  rw [show (∫ x, ψ x * ψ x) = innerProduct ψ ψ from rfl, this, mul_one]

end DFT
