/-
  座標スケーリング変換

  密度の一様座標スケーリング ρ_γ(x) = γ · ρ(γx) を定義し、
  その基本的性質と、汎関数のスケーリング則を形式化する。

  スケーリング則は交換相関汎関数が満たすべき厳密条件の一つ:
    - 交換エネルギー: E_x[ρ_γ] = γ · E_x[ρ]（1次同次）
    - 相関エネルギー: E_c[ρ_γ] > γ · E_c[ρ]（γ > 1 のとき）
-/
import AutoStudy.DFT.Basic

open MeasureTheory DFT

noncomputable section

namespace DFT

/-- 1次元座標スケーリング: ρ_γ(x) = γ · ρ(γx)
    粒子数保存: ∫ ρ_γ(x) dx = ∫ ρ(x) dx（変数変換 u = γx により） -/
def scaledDensity (γ : ℝ) (ρ : ℝ → ℝ) : ℝ → ℝ :=
  fun x => γ * ρ (γ * x)

/-- スケーリングされた密度は非負（元の密度が非負かつ γ > 0 の場合） -/
theorem scaledDensity_nonneg {γ : ℝ} (hγ : 0 < γ) {ρ : ℝ → ℝ}
    (hρ : ∀ x, 0 ≤ ρ x) (x : ℝ) :
    0 ≤ scaledDensity γ ρ x :=
  mul_nonneg (le_of_lt hγ) (hρ _)

/-- γ = 1 のスケーリングは恒等変換 -/
theorem scaledDensity_one (ρ : ℝ → ℝ) :
    scaledDensity 1 ρ = ρ := by
  ext x; simp [scaledDensity]

/-- スケーリングの合成: (ρ_{γ₁})_{γ₂} = ρ_{γ₁·γ₂} -/
theorem scaledDensity_comp (γ₁ γ₂ : ℝ) (ρ : ℝ → ℝ) :
    scaledDensity γ₂ (scaledDensity γ₁ ρ) = scaledDensity (γ₁ * γ₂) ρ := by
  ext x
  unfold scaledDensity
  have h : γ₁ * (γ₂ * x) = γ₁ * γ₂ * x := by ring
  rw [h]; ring

/-- 交換エネルギーのスケーリング則: E_x[ρ_γ] = γ · E_x[ρ]（1次同次） -/
def SatisfiesExchangeScaling (E_x : (ℝ → ℝ) → ℝ) : Prop :=
  ∀ γ > 0, ∀ ρ, E_x (scaledDensity γ ρ) = γ * E_x ρ

/-- 相関エネルギーのスケーリング不等式: γ > 1 のとき E_c[ρ_γ] > γ · E_c[ρ] -/
def SatisfiesCorrelationScalingInequality (E_c : (ℝ → ℝ) → ℝ) : Prop :=
  ∀ γ > 1, ∀ ρ, γ * E_c ρ < E_c (scaledDensity γ ρ)

/-- スケーリング則が恒等変換で整合: E_x[ρ₁] = 1 · E_x[ρ] = E_x[ρ] -/
theorem exchange_scaling_identity {E_x : (ℝ → ℝ) → ℝ}
    (hscale : SatisfiesExchangeScaling E_x) (ρ : ℝ → ℝ) :
    E_x (scaledDensity 1 ρ) = E_x ρ := by
  rw [hscale 1 one_pos ρ, one_mul]

end DFT
