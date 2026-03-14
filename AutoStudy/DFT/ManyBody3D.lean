/-
  3 次元・複素・多電子モデル

  より現実的な DFT の基盤として、3 次元位置空間、複素波動関数、
  多電子配置、反対称性、粒子数保存、N-表現可能性の最小版を定義する。

  設計:
  - ManyBodyState3D: density / particle_number は DensityProjection3D から導出
  - ManyBodyGroundState3D: isNormalized / expectation は ManyBodyInnerProduct3D から導出
  - energy は eigenstate + normalization から E₀ = ⟨Ψ₀|H|Ψ₀⟩ として導出
-/
import AutoStudy.DFT.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section

open Finset Complex MeasureTheory

namespace DFT

-- ============================================================
-- 基本的な 3D 定義
-- ============================================================

/-- 3 次元 1 粒子密度 |ψ|^2。 -/
def probabilityDensity3D (ψ : SingleWavefunction3D) : Position3D → ℝ :=
  fun x => Complex.normSq (ψ x)

/-- 3 次元実空間の密度積分。 -/
def densityIntegral3D (ρ : Position3D → ℝ) : ℝ :=
  ∫ x, ρ x ∂MeasureTheory.Measure.pi
    (fun _ : Fin 3 => (MeasureTheory.volume : MeasureTheory.Measure ℝ))

/-- 多体波動関数の配置空間密度 |Ψ|^2。 -/
def manyBodyProbabilityDensity {N : ℕ}
    (Ψ : ManyBodyWavefunction3D N) : Configuration3D N → ℝ :=
  fun X => Complex.normSq (Ψ X)

/-- 波動関数由来の 1 粒子密度を与える抽象化。
    density_determined_by_probability により、
    密度が |Ψ|² のみから決まることが保証され、
    densityOf が波動関数の位相に依存しない物理的な 1 体密度であることを表す。 -/
structure DensityProjection3D (N : ℕ) where
  densityOf : ManyBodyWavefunction3D N → Position3D → ℝ
  nonneg : ∀ Ψ x, 0 ≤ densityOf Ψ x
  integral_eq_particleNumber : ∀ Ψ, densityIntegral3D (densityOf Ψ) = N
  /-- 密度は確率分布 |Ψ|² のみから決まる:
      2 つの波動関数が同じ |Ψ|² を持てば同じ密度を与える。
      これは 1 体縮約密度行列の対角成分が |Ψ|² の marginal であることの帰結。 -/
  density_determined_by_probability : ∀ Ψ₁ Ψ₂,
    (∀ X, Complex.normSq (Ψ₁ X) = Complex.normSq (Ψ₂ X)) →
    densityOf Ψ₁ = densityOf Ψ₂

/-- 3 次元 1 粒子密度は非負。 -/
theorem probabilityDensity3D_nonneg (ψ : SingleWavefunction3D) (x : Position3D) :
    0 ≤ probabilityDensity3D ψ x :=
  Complex.normSq_nonneg _

/-- 多体配置密度は非負。 -/
theorem manyBodyProbabilityDensity_nonneg {N : ℕ}
    (Ψ : ManyBodyWavefunction3D N) (X : Configuration3D N) :
    0 ≤ manyBodyProbabilityDensity Ψ X :=
  Complex.normSq_nonneg _

-- ============================================================
-- 電子交換と反対称性
-- ============================================================

/-- 電子 i と j を交換した配置。 -/
def swapElectrons {N : ℕ} (i j : Fin N) (X : Configuration3D N) : Configuration3D N :=
  X ∘ Equiv.swap i j

/-- 電子交換は 2 回適用すると元に戻る。 -/
theorem swapElectrons_involutive {N : ℕ} (i j : Fin N) :
    Function.Involutive (swapElectrons i j : Configuration3D N → Configuration3D N) := by
  intro X
  ext k
  simp [swapElectrons]

/-- i 番目と j 番目の位置が一致すれば、交換しても配置は不変。 -/
theorem swapElectrons_eq_self_of_eq {N : ℕ}
    {X : Configuration3D N} {i j : Fin N} (hX : X i = X j) :
    swapElectrons i j X = X := by
  ext k
  by_cases hk : k = i
  · subst hk
    simp [swapElectrons, hX]
  · by_cases hk' : k = j
    · subst hk'
      simp [swapElectrons, hX]
    · rw [show swapElectrons i j X k = X ((Equiv.swap i j) k) by rfl]
      rw [Equiv.swap_apply_of_ne_of_ne hk hk']

/-- フェルミオンの反対称性。 -/
def IsAntisymmetric {N : ℕ} (Ψ : ManyBodyWavefunction3D N) : Prop :=
  ∀ i j, i ≠ j → ∀ X, Ψ (swapElectrons i j X) = -Ψ X

/-- 反対称な波動関数の確率密度は電子交換で不変。 -/
theorem manyBodyProbabilityDensity_swap {N : ℕ}
    {Ψ : ManyBodyWavefunction3D N} (hΨ : IsAntisymmetric Ψ)
    {i j : Fin N} (hij : i ≠ j) (X : Configuration3D N) :
    manyBodyProbabilityDensity Ψ (swapElectrons i j X) =
      manyBodyProbabilityDensity Ψ X := by
  unfold manyBodyProbabilityDensity
  rw [hΨ i j hij X, Complex.normSq_neg]

/-- 反対称性と固定点条件から、波動関数はその配置で 0。 -/
theorem antisymmetric_zero_of_fixed_swap {N : ℕ}
    {Ψ : ManyBodyWavefunction3D N} (hΨ : IsAntisymmetric Ψ)
    {i j : Fin N} (hij : i ≠ j) {X : Configuration3D N}
    (hfix : swapElectrons i j X = X) :
    Ψ X = 0 := by
  have hanti : Ψ X = -Ψ X := by
    simpa [hfix] using hΨ i j hij X
  have hsum : Ψ X + Ψ X = 0 := by
    calc
      Ψ X + Ψ X = -Ψ X + Ψ X := by
        simpa using congrArg (fun z : ℂ => z + Ψ X) hanti
      _ = 0 := by simp
  have hmul : (2 : ℂ) * Ψ X = 0 := by
    simpa [two_mul] using hsum
  exact (mul_eq_zero.mp hmul).resolve_left two_ne_zero

/-- 同じ位置に 2 電子がある配置では、反対称波動関数は 0。 -/
theorem antisymmetric_zero_of_position_eq {N : ℕ}
    {Ψ : ManyBodyWavefunction3D N} (hΨ : IsAntisymmetric Ψ)
    {i j : Fin N} (hij : i ≠ j) {X : Configuration3D N}
    (hX : X i = X j) :
    Ψ X = 0 :=
  antisymmetric_zero_of_fixed_swap hΨ hij (swapElectrons_eq_self_of_eq hX)

-- ============================================================
-- 多電子状態
-- ============================================================

/-- 3 次元多電子状態。 -/
structure ManyBodyState3D (N : ℕ) where
  wavefunction : ManyBodyWavefunction3D N
  projection : DensityProjection3D N
  antisymmetric : IsAntisymmetric wavefunction

namespace ManyBodyState3D

variable {N : ℕ}

def density (state : ManyBodyState3D N) : Position3D → ℝ :=
  state.projection.densityOf state.wavefunction

theorem density_nonneg (state : ManyBodyState3D N) :
    ∀ x, 0 ≤ state.density x :=
  fun x => state.projection.nonneg _ x

theorem density_integral_eq_N (state : ManyBodyState3D N) :
    densityIntegral3D state.density = N :=
  state.projection.integral_eq_particleNumber _

theorem wavefunction_antisymmetric (state : ManyBodyState3D N) :
    IsAntisymmetric state.wavefunction :=
  state.antisymmetric

end ManyBodyState3D

/-- 3 次元多電子状態による N-表現可能性。 -/
def IsNRepresentable3D (N : ℕ) (ρ : Position3D → ℝ) : Prop :=
  ∃ state : ManyBodyState3D N, state.density = ρ

theorem nRepresentable3D_nonneg {N : ℕ} {ρ : Position3D → ℝ}
    (hρ : IsNRepresentable3D N ρ) :
    ∀ x, 0 ≤ ρ x := by
  rcases hρ with ⟨state, rfl⟩
  exact state.density_nonneg

theorem nRepresentable3D_integral {N : ℕ} {ρ : Position3D → ℝ}
    (hρ : IsNRepresentable3D N ρ) :
    densityIntegral3D ρ = N := by
  rcases hρ with ⟨state, rfl⟩
  exact state.density_integral_eq_N

-- ============================================================
-- 多体内積 (Task 1: 独立フィールド削減の基盤)
-- ============================================================

/-- 多体波動関数の ℂ 値内積。
    複素 Hilbert 空間の内積として、共役対称性・正定値性・第 2 引数の線形性を持つ。
    物理学の慣習に従い、第 1 引数に反線形、第 2 引数に線形 (physicist convention)。

    isNormalized / expectation をハミルトニアンから導出するための基盤。 -/
structure ManyBodyInnerProduct3D (N : ℕ) where
  inner : ManyBodyWavefunction3D N → ManyBodyWavefunction3D N → ℂ
  /-- 共役対称性: ⟨Ψ|Φ⟩ = conj(⟨Φ|Ψ⟩) -/
  conjugate_symmetric : ∀ Ψ Φ, inner Ψ Φ = starRingEnd ℂ (inner Φ Ψ)
  /-- 正定値性: ⟨Ψ|Ψ⟩ ≥ 0 -/
  positive_definite : ∀ Ψ, 0 ≤ (inner Ψ Ψ).re
  /-- 非退化性: ⟨Ψ|Ψ⟩ = 0 ⇔ Ψ = 0 -/
  definite : ∀ Ψ, inner Ψ Ψ = 0 → ∀ X, Ψ X = 0
  /-- 第 2 引数の線形性 (スカラー倍): ⟨Ψ | cΦ⟩ = c ⟨Ψ|Φ⟩ -/
  linear_right : ∀ (c : ℂ) Ψ Φ,
    inner Ψ (fun X => c * Φ X) = c * inner Ψ Φ
  /-- 第 2 引数の加法性: ⟨Ψ | Φ₁ + Φ₂⟩ = ⟨Ψ|Φ₁⟩ + ⟨Ψ|Φ₂⟩ -/
  additive_right : ∀ Ψ Φ₁ Φ₂,
    inner Ψ (fun X => Φ₁ X + Φ₂ X) = inner Ψ Φ₁ + inner Ψ Φ₂

namespace ManyBodyInnerProduct3D

variable {N : ℕ} (ip : ManyBodyInnerProduct3D N)

/-- 共役対称性より ⟨Ψ|Ψ⟩ は実数。 -/
theorem inner_self_real (Ψ : ManyBodyWavefunction3D N) :
    (ip.inner Ψ Ψ).im = 0 := by
  have h := ip.conjugate_symmetric Ψ Ψ
  have him : (ip.inner Ψ Ψ).im = -(ip.inner Ψ Ψ).im := by
    conv_lhs => rw [h]
    simp [Complex.conj_im]
  linarith

/-- 正規化条件 (内積から導出): ⟨Ψ|Ψ⟩ = 1 -/
def isNormalized (Ψ : ManyBodyWavefunction3D N) : Prop :=
  ip.inner Ψ Ψ = 1

/-- 演算子の期待値 (内積から導出): Re⟨Ψ|AΨ⟩
    自己共役演算子に対しては虚部が 0 となるが、
    一般的に実部を取ることで ℝ 値の物理量を得る。 -/
def expectation (A : ManyBodyWavefunction3D N → ManyBodyWavefunction3D N)
    (Ψ : ManyBodyWavefunction3D N) : ℝ :=
  (ip.inner Ψ (A Ψ)).re

/-- 固有状態の期待値は固有値に等しい。 -/
theorem eigenstate_expectation_eq
    (A : ManyBodyWavefunction3D N → ManyBodyWavefunction3D N)
    (Ψ : ManyBodyWavefunction3D N) (E : ℝ)
    (heig : A Ψ = fun X => (↑E : ℂ) * Ψ X)
    (hnorm : ip.isNormalized Ψ) :
    ip.expectation A Ψ = E := by
  unfold expectation isNormalized at *
  rw [heig, ip.linear_right, hnorm, mul_one]
  exact Complex.ofReal_re E

/-- 実スカラー倍の線形性 (linear_right の系) -/
theorem real_smul_right (c : ℝ) (Ψ Φ : ManyBodyWavefunction3D N) :
    ip.inner Ψ (fun X => (↑c : ℂ) * Φ X) = (↑c : ℂ) * ip.inner Ψ Φ :=
  ip.linear_right (↑c) Ψ Φ

end ManyBodyInnerProduct3D

-- ============================================================
-- 3 次元多電子ハミルトニアン (toOperator を先に定義)
-- ============================================================

/-- 3 次元多電子ハミルトニアンの最小モデル。 -/
structure ManyBodyHamiltonian3D (N : ℕ) where
  kinetic : ManyBodyWavefunction3D N → ManyBodyWavefunction3D N
  vExt : Position3D → ℝ
  interaction : Position3D → Position3D → ℝ

namespace ManyBodyHamiltonian3D

variable {N : ℕ} (H : ManyBodyHamiltonian3D N)

/-- 外部ポテンシャルの多電子エネルギー密度。 -/
def externalPotentialEnergy (X : Configuration3D N) : ℝ :=
  ∑ i : Fin N, H.vExt (X i)

/-- 電子間相互作用のエネルギー密度。 -/
def interactionEnergy (X : Configuration3D N) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N,
    if i < j then H.interaction (X i) (X j) else 0

/-- H = T + V_ext + V_ee に対応する多電子演算子。 -/
def toOperator (Ψ : ManyBodyWavefunction3D N) : ManyBodyWavefunction3D N :=
  fun X =>
    H.kinetic Ψ X +
      ((H.externalPotentialEnergy X + H.interactionEnergy X : ℝ) : ℂ) * Ψ X

/-- 多電子演算子の点ごとの形。 -/
theorem toOperator_apply (Ψ : ManyBodyWavefunction3D N) (X : Configuration3D N) :
    H.toOperator Ψ X =
      H.kinetic Ψ X +
        ((H.externalPotentialEnergy X + H.interactionEnergy X : ℝ) : ℂ) * Ψ X :=
  rfl

end ManyBodyHamiltonian3D

-- ============================================================
-- 3 次元多電子の基底状態 (Task 1 & 2: ハミルトニアンから導出)
-- ============================================================

/-- 3 次元多電子の基底状態。
    isNormalized / expectation は独立フィールドではなく
    ManyBodyInnerProduct3D とハミルトニアンから導出される。
    energy_eq により E₀ = ⟨Ψ₀|H|Ψ₀⟩ が保証される。 -/
structure ManyBodyGroundState3D (N : ℕ) where
  hamiltonian : ManyBodyHamiltonian3D N
  state : ManyBodyState3D N
  innerProd : ManyBodyInnerProduct3D N
  E₀ : ℝ
  state_normalized : innerProd.isNormalized state.wavefunction
  /-- E₀ は基底状態の期待値に等しい -/
  energy_eq : innerProd.expectation hamiltonian.toOperator state.wavefunction = E₀
  variational : ∀ Ψ, innerProd.isNormalized Ψ →
    E₀ ≤ innerProd.expectation hamiltonian.toOperator Ψ

namespace ManyBodyGroundState3D

variable {N : ℕ}

/-- 正規化判定 (innerProd から導出) -/
def isNormalized (gs : ManyBodyGroundState3D N) :
    ManyBodyWavefunction3D N → Prop :=
  gs.innerProd.isNormalized

/-- 演算子の期待値 (innerProd + hamiltonian から導出) -/
def expectation (gs : ManyBodyGroundState3D N) :
    ManyBodyWavefunction3D N → ℝ :=
  gs.innerProd.expectation gs.hamiltonian.toOperator

/-- 基底状態エネルギー -/
def energy (gs : ManyBodyGroundState3D N) : ℝ := gs.E₀

/-- 基底状態の期待値はエネルギーに等しい。 -/
theorem expectation_eq_energy (gs : ManyBodyGroundState3D N) :
    gs.expectation gs.state.wavefunction = gs.energy :=
  gs.energy_eq

end ManyBodyGroundState3D

/-- 3 次元密度汎関数の最小抽象。 -/
structure DensityFunctional3D (N : ℕ) where
  energy : (Position3D → ℝ) → ℝ
  admissible : (Position3D → ℝ) → Prop

namespace DensityFunctional3D

variable {N : ℕ} (DF : DensityFunctional3D N)

def MinimizesOnAdmissible (ρ₀ : Position3D → ℝ) : Prop :=
  DF.admissible ρ₀ ∧ ∀ ⦃ρ⦄, DF.admissible ρ → DF.energy ρ₀ ≤ DF.energy ρ

end DensityFunctional3D

/-- 3 次元多電子版の抽象 constrained-search データ。 -/
structure ConstrainedSearchModel3D {N : ℕ}
    (gs : ManyBodyGroundState3D N) (DF : DensityFunctional3D N) where
  ground_admissible : DF.admissible gs.state.density
  ground_energy_eq : DF.energy gs.state.density = gs.energy
  realize : ∀ {ρ}, DF.admissible ρ →
    ∃ state : ManyBodyState3D N,
      state.density = ρ ∧
      gs.isNormalized state.wavefunction ∧
      DF.energy ρ = gs.expectation state.wavefunction

namespace ManyBodyGroundState3D

variable {N : ℕ} (gs : ManyBodyGroundState3D N)

/-- 外部ポテンシャルと密度の組から外部エネルギー寄与を与える抽象データ。 -/
structure ExternalPotentialContribution3D where
  energy : (Position3D → ℝ) → (Position3D → ℝ) → ℝ
  same_density : ∀ {v ρ₁ ρ₂}, ρ₁ = ρ₂ → energy v ρ₁ = energy v ρ₂
  neg_potential : ∀ v ρ, energy (fun x => -v x) ρ = -energy v ρ

/-- 外部ポテンシャル寄与の concrete な積分形 ∫ vρ。 -/
def concreteExternalEnergy3D (v ρ : Position3D → ℝ) : ℝ :=
  ∫ x, v x * ρ x ∂MeasureTheory.Measure.pi
    (fun _ : Fin 3 => (MeasureTheory.volume : MeasureTheory.Measure ℝ))

theorem concreteExternalEnergy3D_same_density
    {v ρ₁ ρ₂ : Position3D → ℝ} (hρ : ρ₁ = ρ₂) :
    concreteExternalEnergy3D v ρ₁ = concreteExternalEnergy3D v ρ₂ := by
  rw [hρ]

theorem concreteExternalEnergy3D_neg_potential
    (v ρ : Position3D → ℝ) :
    concreteExternalEnergy3D (fun x => -v x) ρ = -concreteExternalEnergy3D v ρ := by
  unfold concreteExternalEnergy3D
  have hfun : (fun x => (-v x) * ρ x) = (fun x => -(v x * ρ x)) := by
    ext x; ring
  rw [hfun, integral_neg]

def concreteExternalContribution3D : ExternalPotentialContribution3D where
  energy := concreteExternalEnergy3D
  same_density := fun hρ => concreteExternalEnergy3D_same_density hρ
  neg_potential := fun v ρ => concreteExternalEnergy3D_neg_potential v ρ

/-- 2 つの 3 次元多電子ハミルトニアンが運動項と相互作用項を共有すること。 -/
structure SameCore3D (H₁ H₂ : ManyBodyHamiltonian3D N) : Prop where
  kinetic : H₁.kinetic = H₂.kinetic
  interaction : H₁.interaction = H₂.interaction

/-- 3 次元多電子版 HK の explicit な仮定パッケージ。 -/
structure ExplicitHKData3D (gs₁ gs₂ : ManyBodyGroundState3D N) where
  sameCore : SameCore3D gs₁.hamiltonian gs₂.hamiltonian
  external : ExternalPotentialContribution3D
  norm_cross_12 : gs₁.isNormalized gs₂.state.wavefunction
  norm_cross_21 : gs₂.isNormalized gs₁.state.wavefunction
  expectation_shift_left :
    gs₁.expectation gs₂.state.wavefunction =
      gs₂.energy + external.energy
        (fun x => gs₁.hamiltonian.vExt x - gs₂.hamiltonian.vExt x)
        gs₂.state.density
  expectation_shift_right :
    gs₂.expectation gs₁.state.wavefunction =
      gs₁.energy + external.energy
        (fun x => gs₂.hamiltonian.vExt x - gs₁.hamiltonian.vExt x)
        gs₁.state.density

/-- 基底状態密度は N-表現可能。 -/
theorem density_nRepresentable :
    IsNRepresentable3D N gs.state.density :=
  ⟨gs.state, rfl⟩

theorem density_nonneg (x : Position3D) :
    0 ≤ gs.state.density x :=
  gs.state.density_nonneg x

theorem density_integral :
    densityIntegral3D gs.state.density = N :=
  gs.state.density_integral_eq_N

theorem antisymmetric_wavefunction :
    IsAntisymmetric gs.state.wavefunction :=
  gs.state.antisymmetric

/-- 3 次元多電子版 Rayleigh-Ritz 下界。 -/
theorem rayleigh_ritz_lower_bound
    (Ψ : ManyBodyWavefunction3D N) (hΨ : gs.isNormalized Ψ) :
    gs.energy ≤ gs.expectation Ψ :=
  gs.variational Ψ hΨ

/-- 基底状態波動関数がエネルギー最小化を達成することの言い換え。 -/
theorem rayleigh_ritz_minimizer
    (Ψ : ManyBodyWavefunction3D N) (hΨ : gs.isNormalized Ψ) :
    gs.expectation gs.state.wavefunction = gs.energy ∧
      gs.expectation gs.state.wavefunction ≤ gs.expectation Ψ :=
  ⟨gs.expectation_eq_energy, by rw [gs.expectation_eq_energy]; exact gs.variational Ψ hΨ⟩

/-- 同一ハミルトニアン・同一内積なら基底状態エネルギーは一意。 -/
theorem unique_ground_energy
    (gs₁ gs₂ : ManyBodyGroundState3D N)
    (hH : gs₁.hamiltonian = gs₂.hamiltonian)
    (hIP : gs₁.innerProd = gs₂.innerProd) :
    gs₁.energy = gs₂.energy := by
  unfold energy
  apply le_antisymm
  · have h := gs₁.variational gs₂.state.wavefunction
      (show gs₁.isNormalized gs₂.state.wavefunction from by
        simp only [isNormalized, hIP]; exact gs₂.state_normalized)
    have heq : gs₁.innerProd.expectation gs₁.hamiltonian.toOperator gs₂.state.wavefunction =
        gs₂.innerProd.expectation gs₂.hamiltonian.toOperator gs₂.state.wavefunction := by
      simp only [ManyBodyInnerProduct3D.expectation, hIP, hH]
    rw [heq, gs₂.energy_eq] at h
    exact h
  · have h := gs₂.variational gs₁.state.wavefunction
      (show gs₂.isNormalized gs₁.state.wavefunction from by
        simp only [isNormalized, ← hIP]; exact gs₁.state_normalized)
    have heq : gs₂.innerProd.expectation gs₂.hamiltonian.toOperator gs₁.state.wavefunction =
        gs₁.innerProd.expectation gs₁.hamiltonian.toOperator gs₁.state.wavefunction := by
      simp only [ManyBodyInnerProduct3D.expectation, hIP, hH]
    rw [heq, gs₁.energy_eq] at h
    exact h

/-- 2 つの基底状態のエネルギーを比較するための基本不等式。 -/
theorem compare_ground_energies
    (gs₁ gs₂ : ManyBodyGroundState3D N)
    (hNorm12 : gs₁.isNormalized gs₂.state.wavefunction)
    (hNorm21 : gs₂.isNormalized gs₁.state.wavefunction) :
    gs₁.energy ≤ gs₁.expectation gs₂.state.wavefunction ∧
      gs₂.energy ≤ gs₂.expectation gs₁.state.wavefunction :=
  ⟨gs₁.variational _ hNorm12, gs₂.variational _ hNorm21⟩

/-- 基底状態密度が満たす最小の admissibility 条件。 -/
def DensityAdmissible (ρ : Position3D → ℝ) : Prop :=
  IsNRepresentable3D N ρ ∧ ∀ x, 0 ≤ ρ x

theorem density_admissible :
    DensityAdmissible (N := N) gs.state.density :=
  ⟨gs.density_nRepresentable, gs.state.density_nonneg⟩

/-- 抽象 constrained-search データがあれば、基底状態密度は密度汎関数を最小化する。 -/
theorem ground_state_density_minimizes
    (DF : DensityFunctional3D N)
    (model : ConstrainedSearchModel3D gs DF) :
    DF.MinimizesOnAdmissible gs.state.density := by
  constructor
  · exact model.ground_admissible
  · intro ρ hρ
    rcases model.realize hρ with ⟨state, _, hnorm, henergy⟩
    rw [model.ground_energy_eq, henergy]
    exact gs.variational state.wavefunction hnorm

/-- 3 次元多電子版 Hohenberg-Kohn 第二定理の抽象形。 -/
theorem hohenberg_kohn_second_theorem_3d
    (DF : DensityFunctional3D N)
    (model : ConstrainedSearchModel3D gs DF) :
    DF.MinimizesOnAdmissible gs.state.density :=
  gs.ground_state_density_minimizes DF model

/-- 多電子 3 次元版 Hohenberg-Kohn 第一定理の抽象形。 -/
theorem hohenberg_kohn_first_theorem_3d
    (gs₁ gs₂ : ManyBodyGroundState3D N)
    (_hρ : gs₁.state.density = gs₂.state.density)
    (hvar1 : gs₁.energy < gs₁.expectation gs₂.state.wavefunction)
    (hvar2 : gs₂.energy < gs₂.expectation gs₁.state.wavefunction)
    (δV : ℝ)
    (hpot1 : gs₁.expectation gs₂.state.wavefunction = gs₂.energy + δV)
    (hpot2 : gs₂.expectation gs₁.state.wavefunction = gs₁.energy - δV) :
    False := by
  rw [hpot1] at hvar1
  rw [hpot2] at hvar2
  linarith

/-- 3 次元多電子版 HK 第一定理 (対偶形式):
    厳密変分不等式が成立するとき、基底状態密度は異なる。 -/
theorem hohenberg_kohn_different_density_3d
    (gs₁ gs₂ : ManyBodyGroundState3D N)
    (hvar1 : gs₁.energy < gs₁.expectation gs₂.state.wavefunction)
    (hvar2 : gs₂.energy < gs₂.expectation gs₁.state.wavefunction)
    (δV : ℝ)
    (hpot1 : gs₁.expectation gs₂.state.wavefunction = gs₂.energy + δV)
    (hpot2 : gs₂.expectation gs₁.state.wavefunction = gs₁.energy - δV) :
    gs₁.state.density ≠ gs₂.state.density := by
  intro hρ
  exact hohenberg_kohn_first_theorem_3d gs₁ gs₂ hρ hvar1 hvar2 δV hpot1 hpot2

/-- 3 次元多電子版 HK の explicit 形式。 -/
theorem hohenberg_kohn_first_theorem_3d_explicit
    (gs₁ gs₂ : ManyBodyGroundState3D N)
    (data : ExplicitHKData3D gs₁ gs₂)
    (hρ : gs₁.state.density = gs₂.state.density)
    (hvar1 : gs₁.energy < gs₁.expectation gs₂.state.wavefunction)
    (hvar2 : gs₂.energy < gs₂.expectation gs₁.state.wavefunction) :
    False := by
  let δV : ℝ :=
    data.external.energy
      (fun x => gs₁.hamiltonian.vExt x - gs₂.hamiltonian.vExt x)
      gs₂.state.density
  have hneg :
      data.external.energy
        (fun x => gs₂.hamiltonian.vExt x - gs₁.hamiltonian.vExt x)
        gs₁.state.density = -δV := by
    have hfun : (fun x => gs₂.hamiltonian.vExt x - gs₁.hamiltonian.vExt x) =
        (fun x => -((gs₁.hamiltonian.vExt x - gs₂.hamiltonian.vExt x))) := by
      funext x; ring
    rw [hfun, data.external.neg_potential, data.external.same_density hρ]
  have hpot2 : gs₂.expectation gs₁.state.wavefunction = gs₁.energy - δV := by
    rw [data.expectation_shift_right, hneg]; ring
  exact hohenberg_kohn_first_theorem_3d gs₁ gs₂ hρ hvar1 hvar2 δV
    data.expectation_shift_left hpot2

/-- 1 電子系の条件。 -/
def IsOneElectronState (state : ManyBodyState3D 1) : Prop :=
  densityIntegral3D state.density = 1

theorem one_electron_particle_number (state : ManyBodyState3D 1) :
    IsOneElectronState state := by
  exact_mod_cast state.density_integral_eq_N

/-- 3 次元 Hartree 型エネルギーの抽象版。 -/
def hartreeEnergy3D (W : Position3D → Position3D → ℝ) (ρ : Position3D → ℝ) : ℝ :=
  densityIntegral3D (fun x => ρ x * densityIntegral3D (fun y => W x y * ρ y))

theorem hartreeEnergy3D_nonneg
    (W : Position3D → Position3D → ℝ)
    (hW : ∀ x y, 0 ≤ W x y)
    (ρ : Position3D → ℝ)
    (hρ : ∀ x, 0 ≤ ρ x) :
    0 ≤ hartreeEnergy3D W ρ := by
  unfold hartreeEnergy3D densityIntegral3D
  apply integral_nonneg
  intro x
  apply mul_nonneg (hρ x)
  apply integral_nonneg
  intro y
  exact mul_nonneg (hW x y) (hρ y)

/-- expectation を Hartree 項と外部ポテンシャル項へ分解するための concrete データ。 -/
structure HartreeExternalDecomposition3D (gs : ManyBodyGroundState3D N) where
  W : Position3D → Position3D → ℝ
  E_remainder : (Position3D → ℝ) → ℝ
  expectation_eq : ∀ (state : ManyBodyState3D N),
    gs.isNormalized state.wavefunction →
    gs.expectation state.wavefunction =
      E_remainder state.density +
        hartreeEnergy3D W state.density +
        concreteExternalEnergy3D gs.hamiltonian.vExt state.density

def HartreeExternalDecomposition3D.toDensityFunctional
    (decomp : HartreeExternalDecomposition3D gs) : DensityFunctional3D N where
  energy := fun ρ =>
    decomp.E_remainder ρ +
      hartreeEnergy3D decomp.W ρ +
      concreteExternalEnergy3D gs.hamiltonian.vExt ρ
  admissible := DensityAdmissible (N := N)

theorem expectation_eq_decomposed_energy
    (decomp : HartreeExternalDecomposition3D gs)
    (state : ManyBodyState3D N) (hnorm : gs.isNormalized state.wavefunction) :
    gs.expectation state.wavefunction =
      (decomp.toDensityFunctional (gs := gs)).energy state.density := by
  rw [HartreeExternalDecomposition3D.toDensityFunctional]
  exact decomp.expectation_eq state hnorm

theorem ground_energy_eq_decomposed_energy
    (decomp : HartreeExternalDecomposition3D gs) :
    (decomp.toDensityFunctional (gs := gs)).energy gs.state.density = gs.energy := by
  rw [← gs.expectation_eq_energy]
  exact (expectation_eq_decomposed_energy (gs := gs) decomp
    gs.state gs.state_normalized).symm

/-- 3 次元多電子版の拡張された v-表現可能性:
    密度 ρ がある外部ポテンシャル vExt を持つ N 粒子ハミルトニアンの
    基底状態として実現可能。 -/
structure IsVRepresentable3DFor (N : ℕ) (ρ : Position3D → ℝ) where
  /-- 外部ポテンシャル -/
  vExt : Position3D → ℝ
  /-- 実現する基底状態 -/
  gs : ManyBodyGroundState3D N
  /-- 基底状態ハミルトニアンの外部ポテンシャルが vExt に一致する -/
  potential_eq : gs.hamiltonian.vExt = vExt
  /-- 密度の一致 -/
  density_eq : gs.state.density = ρ

/-- Hamiltonian の性質から ManyBodyGroundState3D を構成するためのインターフェース。
    ManyBodyGroundState3D を直接構成する代わりに、このクラスを経由することで
    変分原理が Hamiltonian + InnerProduct から導出されることを保証する。 -/
class HasGroundState3D (N : ℕ) (H : ManyBodyHamiltonian3D N)
    (ip : ManyBodyInnerProduct3D N) where
  /-- H, ip に対応する基底状態 -/
  groundState : ManyBodyGroundState3D N
  /-- 基底状態のハミルトニアンが H に一致する -/
  hamiltonian_eq : groundState.hamiltonian = H
  /-- 基底状態の内積が ip に一致する -/
  innerProd_eq : groundState.innerProd = ip

end ManyBodyGroundState3D

-- ============================================================
-- ハミルトニアンの追加的な性質
-- ============================================================

namespace ManyBodyHamiltonian3D

variable {N : ℕ} (H : ManyBodyHamiltonian3D N)

theorem externalPotentialEnergy_nonneg
    (hv : ∀ x, 0 ≤ H.vExt x) (X : Configuration3D N) :
    0 ≤ H.externalPotentialEnergy X := by
  unfold externalPotentialEnergy
  exact Finset.sum_nonneg fun i _ => hv (X i)

theorem interactionEnergy_nonneg
    (hw : ∀ x y, 0 ≤ H.interaction x y) (X : Configuration3D N) :
    0 ≤ H.interactionEnergy X := by
  unfold interactionEnergy
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  by_cases hij : i < j
  · simp [hij, hw (X i) (X j)]
  · simp [hij]

def externalPotentialDifference
    (H₁ H₂ : ManyBodyHamiltonian3D N) : Position3D → ℝ :=
  fun x => H₁.vExt x - H₂.vExt x

def standardExternalContribution :
    ManyBodyGroundState3D.ExternalPotentialContribution3D :=
  ManyBodyGroundState3D.concreteExternalContribution3D

structure ExpectationShiftData
    (gs₁ gs₂ : ManyBodyGroundState3D N) : Prop where
  norm_cross_12 : gs₁.isNormalized gs₂.state.wavefunction
  norm_cross_21 : gs₂.isNormalized gs₁.state.wavefunction
  shift_left :
    gs₁.expectation gs₂.state.wavefunction =
      gs₂.energy + standardExternalContribution.energy
        (externalPotentialDifference gs₁.hamiltonian gs₂.hamiltonian)
        gs₂.state.density
  shift_right :
    gs₂.expectation gs₁.state.wavefunction =
      gs₁.energy + standardExternalContribution.energy
        (externalPotentialDifference gs₂.hamiltonian gs₁.hamiltonian)
        gs₁.state.density

def toExplicitHKData
    (gs₁ gs₂ : ManyBodyGroundState3D N)
    (hcore : ManyBodyGroundState3D.SameCore3D gs₁.hamiltonian gs₂.hamiltonian)
    (hshift : ExpectationShiftData gs₁ gs₂) :
    ManyBodyGroundState3D.ExplicitHKData3D gs₁ gs₂ where
  sameCore := hcore
  external := standardExternalContribution
  norm_cross_12 := hshift.norm_cross_12
  norm_cross_21 := hshift.norm_cross_21
  expectation_shift_left := by
    simpa [standardExternalContribution, externalPotentialDifference]
      using hshift.shift_left
  expectation_shift_right := by
    simpa [standardExternalContribution, externalPotentialDifference]
      using hshift.shift_right

end ManyBodyHamiltonian3D

end DFT
