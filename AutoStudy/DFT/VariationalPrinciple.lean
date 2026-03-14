/-
  変分原理

  量子力学の変分原理を形式化する。
  任意の正規化された試行波動関数 φ に対して、
  ⟨φ|H|φ⟩ ≥ E₀ (基底状態エネルギー)

  設計:
    - SpectralHamiltonian: ハミルトニアンのスペクトル分解を公理化
    - 変分原理はスペクトル分解から定理として導出
    - GroundState は SpectralHamiltonian から構成

  証明可能な定理:
    - 変分原理 (スペクトル分解からの導出)
    - 基底状態の期待値 = 基底状態エネルギー
    - 基底状態は期待値を最小化する
    - 非縮退基底状態に対する厳密不等式
-/
import AutoStudy.DFT.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order

open DFT

namespace DFT

-- ============================================================
-- スペクトル分解に基づくハミルトニアン
-- ============================================================

/-- スペクトル分解を持つハミルトニアン。
    自己共役性・完全正規直交基底・固有値の単調性を公理化し、
    変分原理を定理として導出する基盤。

    物理的根拠: 自己共役演算子のスペクトル定理により、
    固有状態は完全正規直交系をなし、任意の状態を展開できる。
    変分原理は「⟨ψ|H|ψ⟩ = Σ |cₙ|² Eₙ ≥ E₀ Σ |cₙ|² = E₀」から従う。 -/
structure SpectralHamiltonian where
  /-- ハミルトニアン演算子 -/
  H : (ℝ → ℝ) → ℝ → ℝ
  /-- 固有値列 (昇順) -/
  eigenvalues : ℕ → ℝ
  /-- 固有状態列 (完全正規直交系) -/
  eigenstates : ℕ → (ℝ → ℝ)
  /-- 各固有状態は正規化されている -/
  eigenstates_normalized : ∀ n, IsNormalized (eigenstates n)
  /-- 固有状態は直交 -/
  eigenstates_orthogonal : ∀ m n, m ≠ n →
    innerProduct (eigenstates m) (eigenstates n) = 0
  /-- 固有値方程式: H φₙ = Eₙ φₙ -/
  eigenvalue_eq : ∀ n, IsEigenstate H (eigenstates n) (eigenvalues n)
  /-- 固有値は昇順 -/
  eigenvalues_ordered : Monotone eigenvalues
  /-- スペクトル展開の係数を与える写像 -/
  coefficients : (ℝ → ℝ) → ℕ → ℝ
  /-- 正規化状態に対する係数の二乗和は 1 -/
  coefficients_sum_one : ∀ ψ, IsNormalized ψ →
    HasSum (fun n => (coefficients ψ n) ^ 2) 1
  /-- Parseval の等式: ⟨ψ|H|ψ⟩ = Σ |cₙ|² Eₙ -/
  parseval_H : ∀ ψ, IsNormalized ψ →
    HasSum (fun n => (coefficients ψ n) ^ 2 * eigenvalues n)
      (expectationValue H ψ)

namespace SpectralHamiltonian

variable (SH : SpectralHamiltonian)

/-- 変分原理: 任意の正規化状態に対して ⟨ψ|H|ψ⟩ ≥ E₀。
    証明: Σ cₙ² Eₙ ≥ E₀ Σ cₙ² = E₀
    (∵ Eₙ ≥ E₀ かつ cₙ² ≥ 0) -/
theorem variational_principle (ψ : ℝ → ℝ) (hψ : IsNormalized ψ) :
    SH.eigenvalues 0 ≤ expectationValue SH.H ψ := by
  have hcoeff := SH.coefficients_sum_one ψ hψ
  have hparseval := SH.parseval_H ψ hψ
  have hconst : HasSum
      (fun n => SH.eigenvalues 0 * (SH.coefficients ψ n) ^ 2)
      (SH.eigenvalues 0) := by
    convert hcoeff.mul_left (SH.eigenvalues 0) using 1
    exact (mul_one _).symm
  have hle : ∀ n,
      SH.eigenvalues 0 * (SH.coefficients ψ n) ^ 2 ≤
        (SH.coefficients ψ n) ^ 2 * SH.eigenvalues n := by
    intro n
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left
      (SH.eigenvalues_ordered (Nat.zero_le n)) (sq_nonneg _)
  exact hasSum_le hle hconst hparseval

end SpectralHamiltonian

/-- 基底状態: ハミルトニアン H の固有状態 ψ₀ で、
    変分原理 (任意の正規化波動関数に対して期待値が最小) を満たすもの。

    SpectralHamiltonian.toGroundState により、スペクトル分解から構成できる。
    変分原理は SpectralHamiltonian.variational_principle により証明される。 -/
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

/-- SpectralHamiltonian から GroundState を構成する。
    変分原理は仮定ではなく、スペクトル分解から証明される。 -/
def SpectralHamiltonian.toGroundState (SH : SpectralHamiltonian) :
    GroundState where
  H := SH.H
  ψ₀ := SH.eigenstates 0
  E₀ := SH.eigenvalues 0
  eigenstate := SH.eigenvalue_eq 0
  normalized := SH.eigenstates_normalized 0
  variational := fun φ hφ => SH.variational_principle φ hφ

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

/-- Hamiltonian の性質から GroundState を構成するためのインターフェース。
    GroundState を直接構成する代わりに、このクラスを経由することで
    変分原理が Hamiltonian のスペクトル性質から導出されることを保証する。

    推奨: GroundState を直接作るより、SpectralHamiltonian.toGroundState
    または HasGroundState 経由で構成すべき。 -/
class HasGroundState (H : (ℝ → ℝ) → ℝ → ℝ) where
  /-- H に対応する基底状態 -/
  groundState : GroundState
  /-- 基底状態のハミルトニアンが H に一致する -/
  hamiltonian_eq : groundState.H = H

namespace HasGroundState

variable {H : (ℝ → ℝ) → ℝ → ℝ} [inst : HasGroundState H]

/-- HasGroundState から基底状態エネルギーを取得する。 -/
def energy : ℝ := inst.groundState.E₀

/-- HasGroundState から基底状態波動関数を取得する。 -/
def wavefunction : ℝ → ℝ := inst.groundState.ψ₀

/-- 変分原理: HasGroundState 経由。 -/
theorem variational (φ : ℝ → ℝ) (hφ : IsNormalized φ) :
    inst.groundState.E₀ ≤ expectationValue H φ := by
  have h := inst.groundState.variational φ hφ
  rw [inst.hamiltonian_eq] at h
  exact h

end HasGroundState

/-- SpectralHamiltonian から HasGroundState インスタンスを構成する。 -/
instance SpectralHamiltonian.toHasGroundState (SH : SpectralHamiltonian) :
    HasGroundState SH.H where
  groundState := SH.toGroundState
  hamiltonian_eq := rfl

end DFT
