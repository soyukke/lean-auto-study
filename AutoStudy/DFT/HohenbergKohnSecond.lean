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

/-- N-表現可能密度 (1D): N 個の正規直交軌道の密度の和として表現可能。
    多電子 DFT における N-representability の 1D 簡略化版。
    密度 ρ(x) = Σᵢ |φᵢ(x)|² となる N 個の正規化軌道 φᵢ が存在する。
    注意: これは v-表現可能性より弱い条件であり、
    波動関数がある外部ポテンシャルの基底状態であることは要求しない。 -/
def IsNRepresentable1D (N : ℕ) (ρ : ℝ → ℝ) : Prop :=
  ∃ orbitals : Fin N → (ℝ → ℝ),
    (∀ i, IsNormalized (orbitals i)) ∧
    ρ = fun x => ∑ i : Fin N, electronDensity (orbitals i) x

/-- v-表現可能密度: ある外部ポテンシャルの基底状態密度として実現可能。
    これは N-表現可能性より強い条件であり、
    密度が具体的なハミルトニアンの基底状態から来ることを要求する。 -/
def IsVRepresentable (ρ : ℝ → ℝ) : Prop :=
  ∃ gs : GroundState, electronDensity gs.ψ₀ = ρ

/-- エネルギー汎関数 E[ρ] = F[ρ] + ∫ v_ext(x) · ρ(x) dx
    F: 普遍汎関数 (運動エネルギー + 電子間相互作用) -/
noncomputable def energyFunctional (F : (ℝ → ℝ) → ℝ) (v_ext : ℝ → ℝ) (ρ : ℝ → ℝ) : ℝ :=
  F ρ + ∫ x, v_ext x * ρ x

/-- v-表現可能密度は 1 粒子表現可能 (1D toy model では N=1) -/
theorem isVRepresentable_isNRepresentable {ρ : ℝ → ℝ}
    (h : IsVRepresentable ρ) : IsNRepresentable1D 1 ρ := by
  rcases h with ⟨gs, hρ⟩
  exact ⟨fun _ => gs.ψ₀, fun _ => gs.normalized, by
    ext x; rw [← hρ]; simp⟩

/-- 基底状態密度は v-表現可能 -/
theorem groundState_density_vrepresentable (gs : GroundState) :
    IsVRepresentable (electronDensity gs.ψ₀) :=
  ⟨gs, rfl⟩

/-- 基底状態密度は 1 粒子表現可能 -/
theorem groundState_density_nrepresentable (gs : GroundState) :
    IsNRepresentable1D 1 (electronDensity gs.ψ₀) :=
  ⟨fun _ => gs.ψ₀, fun _ => gs.normalized, by ext x; simp⟩

/-- Hohenberg-Kohn 第二定理 (公理的形式):
    基底状態密度 ρ₀ はエネルギー汎関数 E[ρ] を最小化する。

    注意: この版は hground と hvar を直接仮定しており、
    結論は仮定の trivial な言い換えである。
    本質的な証明は `hohenberg_kohn_second_from_wavefunction_variational` を参照。
    そちらでは波動関数レベルの変分原理 + Levy-Lieb constrained search から
    密度レベルの変分原理を導出している。

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
    各密度に対して、その密度を実現する波動関数上の内部エネルギー下限を与える。

    F_LL[ρ] = min_{ψ→ρ} ⟨ψ|H_internal|ψ⟩
    ここで H_internal は運動エネルギー + 電子間相互作用 (外部ポテンシャルを含まない)。

    attained により infimum が達成されることを保証し、
    波動関数レベルの変分原理から密度レベルの変分原理を導出可能にする。 -/
structure LevyLiebFunctional where
  /-- 内部ハミルトニアン (運動エネルギー + 電子間相互作用) -/
  H_internal : (ℝ → ℝ) → (ℝ → ℝ)
  /-- Levy-Lieb 汎関数 F_LL[ρ] -/
  F_LL : (ℝ → ℝ) → ℝ
  /-- 許容密度の条件 -/
  admissible : (ℝ → ℝ) → Prop
  /-- 許容密度は正規化波動関数で実現可能 -/
  realize : ∀ {ρ}, admissible ρ → ∃ ψ : ℝ → ℝ, IsNormalized ψ ∧ electronDensity ψ = ρ
  /-- Constrained search 下界:
      F_LL[ρ] は ρ を実現する任意の正規化波動関数に対する
      内部ハミルトニアンの期待値の下界。 -/
  lower_bound : ∀ {ρ ψ}, admissible ρ → IsNormalized ψ → electronDensity ψ = ρ →
    F_LL ρ ≤ expectationValue H_internal ψ
  /-- Constrained search の infimum 達成:
      各許容密度に対して、F_LL[ρ] を達成する波動関数が存在する。
      これにより F_LL[ρ] = min (inf ではなく min) が保証される。 -/
  attained : ∀ {ρ}, admissible ρ →
    ∃ ψ : ℝ → ℝ, IsNormalized ψ ∧ electronDensity ψ = ρ ∧
      F_LL ρ = expectationValue H_internal ψ

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
    ∀ ρ, LL.admissible ρ →
      energyFunctional LL.F_LL v_ext ρ₀ ≤ energyFunctional LL.F_LL v_ext ρ := by
  intro ρ hρ
  exact hohenberg_kohn_second_theorem_constrained LL v_ext ρ₀ E₀ hρ₀ hground hvar ρ hρ

/-- 波動関数レベルの変分原理から密度レベルの変分原理を導出する。
    Hohenberg-Kohn 第二定理の本質的な証明:
    hvar (∀ ρ, E₀ ≤ E[ρ]) を直接仮定するのではなく、
    GroundState の変分原理 + Levy-Lieb constrained search から導く。

    証明の構造:
    1. LL.attained から、F_LL[ρ] を達成する ψ_opt を得る
    2. E₀ ≤ ⟨ψ_opt|H|ψ_opt⟩ (波動関数変分原理)
    3. ⟨ψ_opt|H|ψ_opt⟩ = ⟨ψ_opt|H_internal|ψ_opt⟩ + ∫v·ρ (ハミルトニアン分解)
    4. = F_LL[ρ] + ∫v·ρ = E[ρ] (constrained search の attained) -/
theorem hohenberg_kohn_second_from_wavefunction_variational
    (LL : LevyLiebFunctional) (gs : GroundState) (v_ext : ℝ → ℝ)
    (hH : ∀ ψ, IsNormalized ψ →
      expectationValue gs.H ψ =
        expectationValue LL.H_internal ψ + ∫ x, v_ext x * electronDensity ψ x)
    (_hρ₀ : LL.admissible (electronDensity gs.ψ₀))
    (hground : energyFunctional LL.F_LL v_ext (electronDensity gs.ψ₀) = gs.E₀)
    (ρ : ℝ → ℝ) (hρ : LL.admissible ρ) :
    energyFunctional LL.F_LL v_ext (electronDensity gs.ψ₀) ≤
      energyFunctional LL.F_LL v_ext ρ := by
  rw [hground]
  obtain ⟨ψ_opt, hnorm, hdens, hFLL⟩ := LL.attained hρ
  have hvar := gs.variational ψ_opt hnorm
  rw [hH ψ_opt hnorm, hdens] at hvar
  unfold energyFunctional
  linarith [hFLL.symm.le]

/-- 3D 多電子の density functional を 1D 側の Levy-Lieb 風抽象へ落とすための最小インターフェース。 -/
structure LevyLiebBridge3D (N : ℕ) where
  DF3D : DensityFunctional3D N
  to1D : (Fin 3 → ℝ) → ℝ
  admissible_respects_projection : ∀ ρ, DF3D.admissible ρ →
    IsNRepresentable1D N (fun x => ρ (fun _ => to1D (fun _ => x)))

/-- ManyBody3D 側の minimization principle は Levy-Lieb 風の constrained-search の見方と整合する。 -/
theorem manyBody_second_theorem_bridge
    {N : ℕ} (gs : ManyBodyGroundState3D N)
    (DF : DensityFunctional3D N)
    (model : ConstrainedSearchModel3D gs DF) :
    DF.MinimizesOnAdmissible gs.state.density :=
  gs.hohenberg_kohn_second_theorem_3d DF model

end DFT
