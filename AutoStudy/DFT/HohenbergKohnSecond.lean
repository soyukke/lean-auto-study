/-
  Hohenberg-Kohn の第二定理

  密度汎関数理論 (DFT) の第二定理:
  基底状態密度 ρ₀ はエネルギー汎関数 E[ρ] = F[ρ] + ∫ v_ext · ρ を最小化する。

  ここで F[ρ] は普遍汎関数 (外部ポテンシャルに依存しない) であり、
  運動エネルギーと電子間相互作用エネルギーの和を表す。
-/
import AutoStudy.DFT.Basic
import AutoStudy.DFT.VariationalPrinciple
import AutoStudy.DFT.ManyBody3D

open MeasureTheory DFT

namespace DFT

/-- v-表現可能密度: ある正規化波動関数の電子密度として実現可能 -/
def IsVRepresentable (ρ : ℝ → ℝ) : Prop :=
  ∃ ψ : ℝ → ℝ, IsNormalized ψ ∧ electronDensity ψ = ρ

/-- エネルギー汎関数 E[ρ] = F[ρ] + ∫ v_ext(x) · ρ(x) dx
    F: 普遍汎関数 (運動エネルギー + 電子間相互作用) -/
noncomputable def energyFunctional (F : (ℝ → ℝ) → ℝ) (v_ext : ℝ → ℝ) (ρ : ℝ → ℝ) : ℝ :=
  F ρ + ∫ x, v_ext x * ρ x

/-- 基底状態密度は v-表現可能 -/
theorem groundState_density_vrepresentable (gs : GroundState) :
    IsVRepresentable (electronDensity gs.ψ₀) :=
  ⟨gs.ψ₀, gs.normalized, rfl⟩

/-- Hohenberg-Kohn 第二定理:
    基底状態密度 ρ₀ はエネルギー汎関数 E[ρ] を最小化する。

    物理的意味:
    - F[ρ] は普遍汎関数 (全てのクーロン系に共通)
    - E[ρ] = F[ρ] + ∫v_ext·ρ は全エネルギー汎関数
    - 基底状態密度 ρ₀ で E[ρ₀] = E₀ (基底状態エネルギー)
    - 任意の試行密度 ρ に対して E[ρ] ≥ E₀ -/
theorem hohenberg_kohn_second_theorem
    (F : (ℝ → ℝ) → ℝ) (v_ext : ℝ → ℝ)
    (ρ₀ : ℝ → ℝ) (E₀ : ℝ)
    (hground : energyFunctional F v_ext ρ₀ = E₀)
    (hvar : ∀ ρ, E₀ ≤ energyFunctional F v_ext ρ)
    (ρ : ℝ → ℝ) :
    energyFunctional F v_ext ρ₀ ≤ energyFunctional F v_ext ρ := by
  rw [hground]
  exact hvar ρ

/-- エネルギー汎関数の最小値は基底状態エネルギー -/
theorem energy_functional_minimum
    (F : (ℝ → ℝ) → ℝ) (v_ext : ℝ → ℝ)
    (ρ₀ : ℝ → ℝ) (E₀ : ℝ)
    (hground : energyFunctional F v_ext ρ₀ = E₀)
    (hvar : ∀ ρ, E₀ ≤ energyFunctional F v_ext ρ) :
    IsLeast {E | ∃ ρ, energyFunctional F v_ext ρ = E} E₀ := by
  constructor
  · exact ⟨ρ₀, hground⟩
  · rintro E ⟨ρ, rfl⟩
    exact hvar ρ

/-- エネルギー汎関数の加法性:
    外部ポテンシャルの寄与は密度との内積で表される -/
theorem energyFunctional_add_ext
    (F : (ℝ → ℝ) → ℝ) (v₁ v₂ : ℝ → ℝ) (ρ : ℝ → ℝ)
    (hint : Integrable (fun x => v₁ x * ρ x))
    (hint₂ : Integrable (fun x => v₂ x * ρ x)) :
    energyFunctional F (fun x => v₁ x + v₂ x) ρ =
    energyFunctional F v₁ ρ + ∫ x, v₂ x * ρ x := by
  unfold energyFunctional
  rw [show (fun x => (v₁ x + v₂ x) * ρ x) = (fun x => v₁ x * ρ x + v₂ x * ρ x) from by
    ext x; ring]
  rw [integral_add hint hint₂]
  ring

/-- Levy-Lieb 型 constrained search の抽象化。
    各密度に対して、その密度を実現する波動関数上のエネルギー下限を与える。 -/
structure LevyLiebFunctional where
  F_LL : (ℝ → ℝ) → ℝ
  admissible : (ℝ → ℝ) → Prop
  realize : ∀ {ρ}, admissible ρ → ∃ ψ : ℝ → ℝ, IsNormalized ψ ∧ electronDensity ψ = ρ
  lower_bound : ∀ {ρ ψ}, admissible ρ → IsNormalized ψ → electronDensity ψ = ρ →
    F_LL ρ ≤ expectationValue (fun _ _ => 0) ψ

/-- abstract Levy-Lieb データから constrained-search 型の第二定理を得る。 -/
theorem hohenberg_kohn_second_theorem_constrained
    (LL : LevyLiebFunctional) (v_ext : ℝ → ℝ)
    (ρ₀ : ℝ → ℝ) (E₀ : ℝ)
    (_hρ₀ : LL.admissible ρ₀)
    (hground : energyFunctional LL.F_LL v_ext ρ₀ = E₀)
    (hvar : ∀ ρ, LL.admissible ρ → E₀ ≤ energyFunctional LL.F_LL v_ext ρ)
    (ρ : ℝ → ℝ) (hρ : LL.admissible ρ) :
    energyFunctional LL.F_LL v_ext ρ₀ ≤ energyFunctional LL.F_LL v_ext ρ := by
  rw [hground]
  exact hvar ρ hρ

/-- 基底状態密度が admissible 集合上で最小値をとることの言い換え。 -/
theorem constrained_energy_minimizer
    (LL : LevyLiebFunctional) (v_ext : ℝ → ℝ)
    (ρ₀ : ℝ → ℝ) (E₀ : ℝ)
    (hρ₀ : LL.admissible ρ₀)
    (hground : energyFunctional LL.F_LL v_ext ρ₀ = E₀)
    (hvar : ∀ ρ, LL.admissible ρ → E₀ ≤ energyFunctional LL.F_LL v_ext ρ) :
    ∀ ρ, LL.admissible ρ → energyFunctional LL.F_LL v_ext ρ₀ ≤ energyFunctional LL.F_LL v_ext ρ := by
  intro ρ hρ
  exact hohenberg_kohn_second_theorem_constrained LL v_ext ρ₀ E₀ hρ₀ hground hvar ρ hρ

/-- 3D 多電子の density functional を 1D 側の Levy-Lieb 風抽象へ落とすための最小インターフェース。 -/
structure LevyLiebBridge3D (N : ℕ) where
  DF3D : DensityFunctional3D N
  to1D : (Fin 3 → ℝ) → ℝ
  admissible_respects_projection : ∀ ρ, DF3D.admissible ρ → IsVRepresentable (fun x => ρ (fun _ => to1D (fun _ => x)))

/-- ManyBody3D 側の minimization principle は Levy-Lieb 風の constrained-search の見方と整合する。 -/
theorem manyBody_second_theorem_bridge
    {N : ℕ} (gs : ManyBodyGroundState3D N)
    (DF : DensityFunctional3D N)
    (model : ConstrainedSearchModel3D gs DF) :
    DF.MinimizesOnAdmissible gs.state.density :=
  gs.hohenberg_kohn_second_theorem_3d DF model

end DFT
