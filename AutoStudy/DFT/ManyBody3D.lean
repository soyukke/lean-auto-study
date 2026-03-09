/-
  3 次元・複素・多電子モデル

  より現実的な DFT の基盤として、3 次元位置空間、複素波動関数、
  多電子配置、反対称性、粒子数保存、N-表現可能性の最小版を定義する。
  現段階では、積分を含む解析的主張は構造体の公理として保持し、
  交換対称性や多電子ハミルトニアンの代数的性質を機械化する。
-/
import AutoStudy.DFT.Basic
import Mathlib.Data.Complex.Basic

open Finset Complex

namespace DFT

/-- 3 次元位置ベクトル。 -/
abbrev Position3D := Fin 3 → ℝ

/-- 3 次元の 1 粒子複素波動関数。 -/
abbrev SingleWavefunction3D := Position3D → ℂ

/-- N 電子の 3 次元配置。 -/
abbrev Configuration3D (N : ℕ) := Fin N → Position3D

/-- N 電子の多体複素波動関数。 -/
abbrev ManyBodyWavefunction3D (N : ℕ) := Configuration3D N → ℂ

/-- 3 次元 1 粒子密度 |ψ|^2。 -/
def probabilityDensity3D (ψ : SingleWavefunction3D) : Position3D → ℝ :=
  fun x => Complex.normSq (ψ x)

/-- 多体波動関数の配置空間密度 |Ψ|^2。 -/
def manyBodyProbabilityDensity {N : ℕ}
    (Ψ : ManyBodyWavefunction3D N) : Configuration3D N → ℝ :=
  fun X => Complex.normSq (Ψ X)

/-- 3 次元 1 粒子密度は非負。 -/
theorem probabilityDensity3D_nonneg (ψ : SingleWavefunction3D) (x : Position3D) :
    0 ≤ probabilityDensity3D ψ x :=
  Complex.normSq_nonneg _

/-- 多体配置密度は非負。 -/
theorem manyBodyProbabilityDensity_nonneg {N : ℕ}
    (Ψ : ManyBodyWavefunction3D N) (X : Configuration3D N) :
    0 ≤ manyBodyProbabilityDensity Ψ X :=
  Complex.normSq_nonneg _

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

/-- 3 次元多電子状態の最小モデル。
    解析的条件は公理フィールドとして持たせる。 -/
structure ManyBodyState3D (N : ℕ) where
  wavefunction : ManyBodyWavefunction3D N
  normalized : Prop
  antisymmetric : IsAntisymmetric wavefunction
  density : Position3D → ℝ
  density_nonneg : ∀ x, 0 ≤ density x
  particle_number : ℝ
  particle_number_eq : particle_number = N

namespace ManyBodyState3D

variable {N : ℕ} (state : ManyBodyState3D N)

/-- 多電子状態が持つ粒子数は N。 -/
theorem particle_number_conservation :
    state.particle_number = N :=
  state.particle_number_eq

/-- 状態に付随する波動関数は反対称。 -/
theorem wavefunction_antisymmetric :
    IsAntisymmetric state.wavefunction :=
  state.antisymmetric

end ManyBodyState3D

/-- 3 次元多電子状態による N-表現可能性。 -/
def IsNRepresentable3D (N : ℕ) (ρ : Position3D → ℝ) : Prop :=
  ∃ state : ManyBodyState3D N, state.density = ρ

/-- N-表現可能密度は非負。 -/
theorem nRepresentable3D_nonneg {N : ℕ} {ρ : Position3D → ℝ}
    (hρ : IsNRepresentable3D N ρ) :
    ∀ x, 0 ≤ ρ x := by
  rcases hρ with ⟨state, rfl⟩
  exact state.density_nonneg

/-- N-表現可能密度は粒子数 N に対応する状態から来る。 -/
theorem nRepresentable3D_particle_number {N : ℕ} {ρ : Position3D → ℝ}
    (hρ : IsNRepresentable3D N ρ) :
    ∃ state : ManyBodyState3D N, state.density = ρ ∧ state.particle_number = N := by
  rcases hρ with ⟨state, rfl⟩
  exact ⟨state, rfl, state.particle_number_eq⟩

/-- 3 次元多電子ハミルトニアンの最小モデル。 -/
structure ManyBodyHamiltonian3D (N : ℕ) where
  kinetic : ManyBodyWavefunction3D N → ManyBodyWavefunction3D N
  vExt : Position3D → ℝ
  interaction : Position3D → Position3D → ℝ

/-- 3 次元多電子の基底状態の最小抽象。
    期待値と規格化可能性は公理的に持たせる。 -/
structure ManyBodyGroundState3D (N : ℕ) where
  hamiltonian : ManyBodyHamiltonian3D N
  state : ManyBodyState3D N
  energy : ℝ
  isNormalized : ManyBodyWavefunction3D N → Prop
  expectation : ManyBodyWavefunction3D N → ℝ
  state_normalized : isNormalized state.wavefunction
  expectation_eq : expectation state.wavefunction = energy
  variational : ∀ Ψ, isNormalized Ψ → energy ≤ expectation Ψ

namespace ManyBodyGroundState3D

variable {N : ℕ} (gs : ManyBodyGroundState3D N)

/-- 外部ポテンシャルと密度の組から外部エネルギー寄与を与える抽象データ。 -/
structure ExternalPotentialContribution3D where
  energy : (Position3D → ℝ) → (Position3D → ℝ) → ℝ
  same_density : ∀ {v ρ₁ ρ₂}, ρ₁ = ρ₂ → energy v ρ₁ = energy v ρ₂
  neg_potential : ∀ v ρ, energy (fun x => -v x) ρ = -energy v ρ

/-- 2 つの 3 次元多電子ハミルトニアンが運動項と相互作用項を共有すること。 -/
structure SameCore3D (H₁ H₂ : ManyBodyHamiltonian3D N) : Prop where
  kinetic : H₁.kinetic = H₂.kinetic
  interaction : H₁.interaction = H₂.interaction

/-- 3 次元多電子版 HK の explicit な仮定パッケージ。 -/
structure ExplicitHKData3D (gs₁ gs₂ : ManyBodyGroundState3D N) where
  sameCore : SameCore3D gs₁.hamiltonian gs₂.hamiltonian
  external : ExternalPotentialContribution3D
  expectation_shift_left :
    ∀ Ψ ρ E,
      gs₁.expectation Ψ =
        E + external.energy
          (fun x => gs₁.hamiltonian.vExt x - gs₂.hamiltonian.vExt x) ρ
  expectation_shift_right :
    ∀ Ψ ρ E,
      gs₂.expectation Ψ =
        E + external.energy
          (fun x => gs₂.hamiltonian.vExt x - gs₁.hamiltonian.vExt x) ρ

/-- 基底状態密度は N-表現可能。 -/
theorem density_nRepresentable :
    IsNRepresentable3D N gs.state.density :=
  ⟨gs.state, rfl⟩

/-- 基底状態密度は非負。 -/
theorem density_nonneg (x : Position3D) :
    0 ≤ gs.state.density x :=
  gs.state.density_nonneg x

/-- 基底状態は粒子数 N を持つ。 -/
theorem particle_number_eq :
    gs.state.particle_number = N :=
  gs.state.particle_number_eq

/-- 基底状態の波動関数は反対称。 -/
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
      gs.expectation gs.state.wavefunction ≤ gs.expectation Ψ := by
  constructor
  · exact gs.expectation_eq
  · rw [gs.expectation_eq]
    exact gs.variational Ψ hΨ

/-- 同一ハミルトニアン・同一期待値写像なら基底状態エネルギーは一意。 -/
theorem unique_ground_energy
    (gs₁ gs₂ : ManyBodyGroundState3D N)
    (hH : gs₁.hamiltonian = gs₂.hamiltonian)
    (hNorm : gs₁.isNormalized = gs₂.isNormalized)
    (hExp : gs₁.expectation = gs₂.expectation) :
    gs₁.energy = gs₂.energy := by
  let _ := hH
  have hle₁ : gs₁.energy ≤ gs₂.energy := by
    have h := gs₁.variational gs₂.state.wavefunction (by simpa [hNorm] using gs₂.state_normalized)
    rw [hExp, gs₂.expectation_eq] at h
    exact h
  have hle₂ : gs₂.energy ≤ gs₁.energy := by
    have h := gs₂.variational gs₁.state.wavefunction (by simpa [hNorm] using gs₁.state_normalized)
    rw [← hExp, gs₁.expectation_eq] at h
    exact h
  linarith

/-- 2 つの基底状態のエネルギーを比較するための基本不等式。 -/
theorem compare_ground_energies
    (gs₁ gs₂ : ManyBodyGroundState3D N)
    (hNorm12 : gs₁.isNormalized gs₂.state.wavefunction)
    (hNorm21 : gs₂.isNormalized gs₁.state.wavefunction) :
    gs₁.energy ≤ gs₁.expectation gs₂.state.wavefunction ∧
      gs₂.energy ≤ gs₂.expectation gs₁.state.wavefunction := by
  constructor
  · exact gs₁.variational _ hNorm12
  · exact gs₂.variational _ hNorm21

/-- 基底状態密度が満たす最小の admissibility 条件。 -/
def DensityAdmissible (ρ : Position3D → ℝ) : Prop :=
  IsNRepresentable3D N ρ ∧ ∀ x, 0 ≤ ρ x

/-- 基底状態密度は admissible。 -/
theorem density_admissible :
    DensityAdmissible (N := N) gs.state.density := by
  constructor
  · exact gs.density_nRepresentable
  · exact gs.state.density_nonneg

/-- 多電子 3 次元版 Hohenberg-Kohn 第一定理の抽象形。 -/
theorem hohenberg_kohn_first_theorem_3d
    (gs₁ gs₂ : ManyBodyGroundState3D N)
    (hρ : gs₁.state.density = gs₂.state.density)
    (hvar1 : gs₁.energy < gs₁.expectation gs₂.state.wavefunction)
    (hvar2 : gs₂.energy < gs₂.expectation gs₁.state.wavefunction)
    (δV : ℝ)
    (hpot1 : gs₁.expectation gs₂.state.wavefunction = gs₂.energy + δV)
    (hpot2 : gs₂.expectation gs₁.state.wavefunction = gs₁.energy - δV) :
    False := by
  let _ := hρ
  rw [hpot1] at hvar1
  rw [hpot2] at hvar2
  linarith

/-- 3 次元多電子版 HK の explicit 形式。
    共通コアを持つハミルトニアンと外部ポテンシャル差の寄与から矛盾を導く。 -/
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
  have hpot1 : gs₁.expectation gs₂.state.wavefunction = gs₂.energy + δV := by
    simpa [δV] using
      data.expectation_shift_left gs₂.state.wavefunction gs₂.state.density gs₂.energy
  have hδeq :
      data.external.energy
        (fun x => gs₁.hamiltonian.vExt x - gs₂.hamiltonian.vExt x)
        gs₁.state.density = δV := by
    dsimp [δV]
    exact data.external.same_density hρ
  have hneg :
      data.external.energy
        (fun x => gs₂.hamiltonian.vExt x - gs₁.hamiltonian.vExt x)
        gs₁.state.density = -δV := by
    have hfun : (fun x => gs₂.hamiltonian.vExt x - gs₁.hamiltonian.vExt x) =
        (fun x => -((gs₁.hamiltonian.vExt x - gs₂.hamiltonian.vExt x))) := by
      funext x
      ring
    rw [hfun, data.external.neg_potential]
    rw [hδeq]
  have hpot2 : gs₂.expectation gs₁.state.wavefunction = gs₁.energy - δV := by
    have hshift :=
      data.expectation_shift_right gs₁.state.wavefunction gs₁.state.density gs₁.energy
    rw [hshift, hneg]
    ring
  exact hohenberg_kohn_first_theorem_3d gs₁ gs₂ hρ hvar1 hvar2 δV hpot1 hpot2

end ManyBodyGroundState3D

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

/-- 外部ポテンシャルが非負なら外部エネルギー密度も非負。 -/
theorem externalPotentialEnergy_nonneg
    (hv : ∀ x, 0 ≤ H.vExt x) (X : Configuration3D N) :
    0 ≤ H.externalPotentialEnergy X := by
  unfold externalPotentialEnergy
  exact Finset.sum_nonneg fun i _ => hv (X i)

/-- 相互作用ポテンシャルが非負なら相互作用エネルギー密度も非負。 -/
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

/-- 3 次元多電子ハミルトニアンの外部ポテンシャル差。 -/
def externalPotentialDifference
    (H₁ H₂ : ManyBodyHamiltonian3D N) : Position3D → ℝ :=
  fun x => H₁.vExt x - H₂.vExt x

/-- 外部ポテンシャル差を評価するための標準的な contribution。 -/
def standardExternalContribution :
    ManyBodyGroundState3D.ExternalPotentialContribution3D where
  energy v ρ := 0
  same_density := by intro v ρ₁ ρ₂ hρ; simp
  neg_potential := by intro v ρ; simp

/-- 共通コアを持つ 2 つのハミルトニアン間の expectation shift をまとめる補助構造。 -/
structure ExpectationShiftData
    (gs₁ gs₂ : ManyBodyGroundState3D N) : Prop where
  shift_left :
    ∀ Ψ ρ E,
      gs₁.expectation Ψ =
        E + standardExternalContribution.energy
          (externalPotentialDifference gs₁.hamiltonian gs₂.hamiltonian) ρ
  shift_right :
    ∀ Ψ ρ E,
      gs₂.expectation Ψ =
        E + standardExternalContribution.energy
          (externalPotentialDifference gs₂.hamiltonian gs₁.hamiltonian) ρ

/-- Expectation shift データから explicit HK data を作る。 -/
def toExplicitHKData
    (gs₁ gs₂ : ManyBodyGroundState3D N)
    (hcore : ManyBodyGroundState3D.SameCore3D gs₁.hamiltonian gs₂.hamiltonian)
    (hshift : ExpectationShiftData gs₁ gs₂) :
    ManyBodyGroundState3D.ExplicitHKData3D gs₁ gs₂ where
  sameCore := hcore
  external := standardExternalContribution
  expectation_shift_left := by
    intro Ψ ρ E
    simpa [standardExternalContribution, externalPotentialDifference] using hshift.shift_left Ψ ρ E
  expectation_shift_right := by
    intro Ψ ρ E
    simpa [standardExternalContribution, externalPotentialDifference] using hshift.shift_right Ψ ρ E

end ManyBodyHamiltonian3D

end DFT
