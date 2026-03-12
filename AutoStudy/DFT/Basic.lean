/-
  密度汎関数理論 (DFT) の基礎定義

  第一原理計算の数学的基礎を形式化する。
  簡略化のため実数値1粒子波動関数を使用する (1D toy model)。
  3 次元多電子版は ManyBody3D.lean を参照。
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

noncomputable section

open MeasureTheory

namespace DFT

/-- 波動関数の内積 ⟨ψ|φ⟩ = ∫ ψ(x) · φ(x) dx -/
def innerProduct (ψ φ : ℝ → ℝ) : ℝ :=
  ∫ x, ψ x * φ x

/-- 正規化条件: 可積分性を含む ⟨ψ|ψ⟩ = 1。
    integral_undef に依存せず、可積分性を明示的に要求する。 -/
structure IsNormalized (ψ : ℝ → ℝ) : Prop where
  integrable : Integrable (fun x => ψ x * ψ x)
  norm_eq : innerProduct ψ ψ = 1

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

/-- 正規化条件は電子密度の可積分性を含意する。
    IsNormalized に integrable フィールドを持つため直接抽出できる。 -/
theorem isNormalized_integrable (ψ : ℝ → ℝ) (hnorm : IsNormalized ψ) :
    Integrable (electronDensity ψ) :=
  hnorm.integrable

/-- 固有状態条件と正規化条件のもとで、期待値の被積分関数は可積分。
    Aψ = Eψ なら ψ(x)·(Aψ)(x) = E·|ψ(x)|² であり、
    IsNormalized ψ から |ψ|² の可積分性が従う。 -/
theorem eigenstate_integrable (A : (ℝ → ℝ) → (ℝ → ℝ)) (ψ : ℝ → ℝ) (E : ℝ)
    (heig : IsEigenstate A ψ E) (hnorm : IsNormalized ψ) :
    Integrable (fun x => ψ x * A ψ x) := by
  have key : (fun x => ψ x * A ψ x) = (fun x => E * electronDensity ψ x) := by
    ext x; have := congr_fun heig x; unfold electronDensity; rw [this]; ring
  rw [key]
  exact (isNormalized_integrable ψ hnorm).const_mul E

/-- 正規化波動関数の密度の積分は 1 -/
theorem electronDensity_integral_one (ψ : ℝ → ℝ)
    (hnorm : IsNormalized ψ) :
    ∫ x, electronDensity ψ x = 1 := by
  change innerProduct ψ ψ = 1
  exact hnorm.norm_eq

/-- 固有状態の期待値は固有値に等しい:
    Aψ = Eψ かつ ⟨ψ|ψ⟩ = 1 ならば ⟨ψ|A|ψ⟩ = E
    注意: 可積分性は IsNormalized + IsEigenstate から自動的に従う
    (eigenstate_integrable 参照)。 -/
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
  have hone : innerProduct ψ ψ = 1 := hnorm.norm_eq
  change E * ∫ x, ψ x * ψ x = E
  rw [show (∫ x, ψ x * ψ x) = innerProduct ψ ψ from rfl, hone, mul_one]

-- ============================================================
-- 3 次元の基本定義 (ManyBody3D.lean と共有)
-- ============================================================

/-- 3 次元位置ベクトル。 -/
abbrev Position3D := Fin 3 → ℝ

/-- 3 次元の 1 粒子複素波動関数。 -/
abbrev SingleWavefunction3D := Position3D → ℂ

/-- N 電子の 3 次元配置。 -/
abbrev Configuration3D (N : ℕ) := Fin N → Position3D

/-- N 電子の多体複素波動関数。 -/
abbrev ManyBodyWavefunction3D (N : ℕ) := Configuration3D N → ℂ

end DFT
