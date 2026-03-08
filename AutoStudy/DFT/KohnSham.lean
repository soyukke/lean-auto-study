/-
  Kohn-Sham 方程式

  密度汎関数理論の実用的枠組み: 相互作用する多体問題を
  有効1粒子方程式の集合に帰着させる。

  Kohn-Sham の枠組み:
    1. N個の1粒子軌道 φᵢ を導入
    2. 有効ポテンシャル v_eff = v_ext + v_Hartree + v_xc のもとで
       [-∇²/(2m) + v_eff] φᵢ = εᵢ φᵢ  (Kohn-Sham 方程式)
    3. 密度 ρ(x) = Σᵢ |φᵢ(x)|²
    4. v_eff は ρ に依存 → 自己無撞着条件

  証明する定理:
    - Kohn-Sham 密度は非負
    - Kohn-Sham 密度の積分 = 粒子数 N
    - 有効ポテンシャルの分解
    - 自己無撞着条件の定式化
-/
import AutoStudy.DFT.Basic

open MeasureTheory DFT Finset

namespace DFT

/-- Kohn-Sham 系: N個の1粒子軌道からなる系 -/
structure KohnShamSystem (N : ℕ) where
  /-- Kohn-Sham 軌道 φᵢ -/
  orbitals : Fin N → (ℝ → ℝ)
  /-- 軌道エネルギー εᵢ -/
  energies : Fin N → ℝ
  /-- 有効ポテンシャル v_eff -/
  v_eff : ℝ → ℝ
  /-- 各軌道は正規化されている: ⟨φᵢ|φᵢ⟩ = 1 -/
  normalized : ∀ i, IsNormalized (orbitals i)

namespace KohnShamSystem

variable {N : ℕ} (ks : KohnShamSystem N)

/-- Kohn-Sham 密度: ρ(x) = Σᵢ |φᵢ(x)|² = Σᵢ φᵢ(x)² -/
noncomputable def density : ℝ → ℝ :=
  fun x => ∑ i : Fin N, electronDensity (ks.orbitals i) x

/-- Kohn-Sham 密度は非負 -/
theorem density_nonneg (x : ℝ) : 0 ≤ ks.density x :=
  Finset.sum_nonneg fun i _ => electronDensity_nonneg (ks.orbitals i) x

/-- Kohn-Sham 密度の積分は粒子数 N に等しい:
    ∫ ρ(x) dx = Σᵢ ∫ |φᵢ(x)|² dx = Σᵢ 1 = N -/
theorem density_integral
    (hint : ∀ i, Integrable (electronDensity (ks.orbitals i))) :
    ∫ x, ks.density x = ↑N := by
  unfold density
  rw [integral_finset_sum _ (fun i _ => hint i)]
  have h : ∀ i : Fin N, ∫ x, electronDensity (ks.orbitals i) x = 1 :=
    fun i => electronDensity_integral_one _ (ks.normalized i)
  simp_rw [h, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

end KohnShamSystem

/-- 有効ポテンシャルの分解:
    v_eff(x) = v_ext(x) + v_Hartree(x) + v_xc(x) -/
structure EffectivePotential where
  /-- 外部ポテンシャル (原子核からのクーロンポテンシャル) -/
  v_ext : ℝ → ℝ
  /-- Hartree ポテンシャル (電子間の古典的クーロン反発) -/
  v_hartree : ℝ → ℝ
  /-- 交換相関ポテンシャル (量子力学的効果) -/
  v_xc : ℝ → ℝ
  /-- 有効ポテンシャル -/
  v_eff : ℝ → ℝ
  /-- 分解条件: v_eff = v_ext + v_Hartree + v_xc -/
  decomposition : v_eff = fun x => v_ext x + v_hartree x + v_xc x

namespace EffectivePotential

/-- 有効ポテンシャルの点ごとの分解 -/
theorem eval_eq (ep : EffectivePotential) (x : ℝ) :
    ep.v_eff x = ep.v_ext x + ep.v_hartree x + ep.v_xc x :=
  congr_fun ep.decomposition x

end EffectivePotential

/-- Kohn-Sham の自己無撞着条件:
    密度 → 有効ポテンシャル → 軌道 → 密度 の循環が自己無撞着であること。

    v_eff は密度 ρ の汎関数であり、ρ は軌道 φᵢ から構成される。
    自己無撞着とは、v_eff[ρ] から得られる軌道で再計算した密度が
    元の ρ と一致することを意味する。 -/
structure SelfConsistent (N : ℕ) where
  /-- Kohn-Sham 系 -/
  ks : KohnShamSystem N
  /-- 密度から有効ポテンシャルを計算する写像 -/
  potentialFromDensity : (ℝ → ℝ) → (ℝ → ℝ)
  /-- 自己無撞着条件: v_eff = potentialFromDensity(ρ_KS) -/
  consistent : ks.v_eff = potentialFromDensity ks.density

/-- Kohn-Sham 全エネルギー:
    E_KS = Σᵢ εᵢ - E_Hartree[ρ] + E_xc[ρ] - ∫ v_xc(x)ρ(x) dx

    ここでは軌道エネルギーの和として簡略化して定義する。 -/
noncomputable def orbitalEnergySum {N : ℕ} (ks : KohnShamSystem N) : ℝ :=
  ∑ i : Fin N, ks.energies i

/-- 軌道エネルギーの和の別表現 (固有状態なら期待値の和に等しい) -/
theorem orbitalEnergySum_eq_expectation_sum {N : ℕ} (ks : KohnShamSystem N)
    (H_KS : (ℝ → ℝ) → ℝ → ℝ)
    (heig : ∀ i, IsEigenstate H_KS (ks.orbitals i) (ks.energies i)) :
    orbitalEnergySum ks = ∑ i : Fin N, expectationValue H_KS (ks.orbitals i) := by
  unfold orbitalEnergySum
  congr 1
  ext i
  exact (eigenstate_expectation_eq H_KS (ks.orbitals i) (ks.energies i) (heig i)
    (ks.normalized i)).symm

end DFT
