/-
  量子力学演算子の構造

  線形性・自己共役性・定義域を備えた演算子の型を定義する。
  既存の bare 演算子 `(ℝ → ℝ) → (ℝ → ℝ)` と互換性を持つ。
-/
import AutoStudy.DFT.Basic
import AutoStudy.DFT.SelfAdjoint

open MeasureTheory

namespace DFT

-- ============================================================
-- 1D 演算子
-- ============================================================

/-- 定義域付き 1 粒子量子演算子。
    既存の `(ℝ → ℝ) → (ℝ → ℝ)` 型の演算子に
    定義域の情報を付加する。 -/
structure QuantumOperator1D where
  /-- 演算子の作用 -/
  apply : (ℝ → ℝ) → (ℝ → ℝ)
  /-- 定義域: 演算子の作用が well-defined な波動関数の集合 -/
  domain : Set (ℝ → ℝ)

namespace QuantumOperator1D

/-- 演算子の線形性: 加法性とスカラー倍の保存。 -/
structure IsLinear (A : QuantumOperator1D) : Prop where
  add : ∀ {ψ φ}, ψ ∈ A.domain → φ ∈ A.domain →
    A.apply (fun x => ψ x + φ x) = fun x => A.apply ψ x + A.apply φ x
  smul : ∀ {ψ} (c : ℝ), ψ ∈ A.domain →
    A.apply (fun x => c * ψ x) = fun x => c * A.apply ψ x
  domain_add : ∀ {ψ φ}, ψ ∈ A.domain → φ ∈ A.domain →
    (fun x => ψ x + φ x) ∈ A.domain
  domain_smul : ∀ {ψ} (c : ℝ), ψ ∈ A.domain →
    (fun x => c * ψ x) ∈ A.domain

/-- 定義域上の自己共役性 (エルミート性):
    ∀ ψ φ ∈ domain, ⟨ψ|Aφ⟩ = ⟨Aψ|φ⟩ -/
def IsSelfAdjointOn (A : QuantumOperator1D) : Prop :=
  ∀ {ψ φ}, ψ ∈ A.domain → φ ∈ A.domain →
    innerProduct ψ (A.apply φ) = innerProduct (A.apply ψ) φ

/-- bare 演算子から QuantumOperator1D を構成する (定義域 = 全体) -/
def ofBare (A : (ℝ → ℝ) → (ℝ → ℝ)) : QuantumOperator1D where
  apply := A
  domain := Set.univ

/-- 演算子和 -/
def add (A B : QuantumOperator1D) : QuantumOperator1D where
  apply := fun ψ x => A.apply ψ x + B.apply ψ x
  domain := A.domain ∩ B.domain

/-- 演算子スカラー倍 -/
def scalarMul (c : ℝ) (A : QuantumOperator1D) : QuantumOperator1D where
  apply := fun ψ x => c * A.apply ψ x
  domain := A.domain

end QuantumOperator1D

/-- 自己共役線形演算子のバンドル -/
structure HermitianOperator1D extends QuantumOperator1D where
  /-- 線形性 -/
  linear : toQuantumOperator1D.IsLinear
  /-- 自己共役性 -/
  hermitian : toQuantumOperator1D.IsSelfAdjointOn

/-- 全定義域上の自己共役性と既存の DFT.IsSelfAdjoint の同値性 -/
theorem quantumOp_isSelfAdjointOn_iff_isSelfAdjoint (A : (ℝ → ℝ) → (ℝ → ℝ)) :
    (QuantumOperator1D.ofBare A).IsSelfAdjointOn ↔ DFT.IsSelfAdjoint A := by
  constructor
  · intro h
    unfold DFT.IsSelfAdjoint
    intro ψ φ
    exact h (Set.mem_univ ψ) (Set.mem_univ φ)
  · intro h ψ φ _ _
    exact h ψ φ

-- ============================================================
-- 乗法ポテンシャル演算子
-- ============================================================

/-- 乗法ポテンシャル演算子: (Vψ)(x) = v(x) ψ(x) -/
def potentialOp (v : ℝ → ℝ) : QuantumOperator1D where
  apply := fun ψ x => v x * ψ x
  domain := Set.univ

/-- ポテンシャル演算子は線形 -/
theorem potentialOp_linear (v : ℝ → ℝ) :
    (potentialOp v).IsLinear where
  add := by intro ψ φ _ _; ext x; simp [potentialOp]; ring
  smul := by intro ψ c _; ext x; simp [potentialOp]; ring
  domain_add := by intro _ _ _ _; exact Set.mem_univ _
  domain_smul := by intro _ c _; exact Set.mem_univ _

/-- ポテンシャル演算子は自己共役 (実数値の場合) -/
theorem potentialOp_selfAdjoint (v : ℝ → ℝ) :
    (potentialOp v).IsSelfAdjointOn := by
  intro ψ φ _ _
  unfold potentialOp innerProduct
  congr 1; ext x; ring

/-- ポテンシャル演算子の Hermitian バンドル -/
def potentialHermitianOp (v : ℝ → ℝ) : HermitianOperator1D where
  toQuantumOperator1D := potentialOp v
  linear := potentialOp_linear v
  hermitian := potentialOp_selfAdjoint v

/-- 演算子和の線形性 -/
theorem QuantumOperator1D.add_linear {A B : QuantumOperator1D}
    (hA : A.IsLinear) (hB : B.IsLinear) :
    (A.add B).IsLinear where
  add := by
    intro ψ φ ⟨hψA, hψB⟩ ⟨hφA, hφB⟩
    ext x; simp only [QuantumOperator1D.add]
    have hA' := congr_fun (hA.add hψA hφA) x
    have hB' := congr_fun (hB.add hψB hφB) x
    linarith
  smul := by
    intro ψ c ⟨hψA, hψB⟩
    ext x; simp only [QuantumOperator1D.add]
    have hA' := congr_fun (hA.smul c hψA) x
    have hB' := congr_fun (hB.smul c hψB) x
    linarith
  domain_add := by
    intro ψ φ ⟨hψA, hψB⟩ ⟨hφA, hφB⟩
    exact ⟨hA.domain_add hψA hφA, hB.domain_add hψB hφB⟩
  domain_smul := by
    intro ψ c ⟨hψA, hψB⟩
    exact ⟨hA.domain_smul c hψA, hB.domain_smul c hψB⟩

/-- 演算子和の自己共役性 -/
theorem QuantumOperator1D.add_selfAdjoint {A B : QuantumOperator1D}
    (hA : A.IsSelfAdjointOn) (hB : B.IsSelfAdjointOn)
    (hint : ∀ {ψ φ}, ψ ∈ A.domain ∩ B.domain → φ ∈ A.domain ∩ B.domain →
      Integrable (fun x => ψ x * A.apply φ x) ∧
      Integrable (fun x => ψ x * B.apply φ x)) :
    (A.add B).IsSelfAdjointOn := by
  intro ψ φ hψ hφ
  unfold QuantumOperator1D.add innerProduct
  have hfL : (fun x => ψ x * (A.apply φ x + B.apply φ x)) =
      (fun x => ψ x * A.apply φ x + ψ x * B.apply φ x) := by ext x; ring
  have hfR : (fun x => (A.apply ψ x + B.apply ψ x) * φ x) =
      (fun x => φ x * A.apply ψ x + φ x * B.apply ψ x) := by ext x; ring
  rw [hfL, hfR]
  rw [integral_add (hint hψ hφ).1 (hint hψ hφ).2,
      integral_add (hint hφ hψ).1 (hint hφ hψ).2]
  -- hA : ⟨ψ|Aφ⟩ = ⟨Aψ|φ⟩, hB : ⟨ψ|Bφ⟩ = ⟨Bψ|φ⟩
  -- ⟨Aψ|φ⟩ = ∫(Aψ)·φ, but RHS has ∫φ·(Aψ), need commutativity
  have hcommA : (∫ x, A.apply ψ x * φ x) = ∫ x, φ x * A.apply ψ x := by
    congr 1; ext x; ring
  have hcommB : (∫ x, B.apply ψ x * φ x) = ∫ x, φ x * B.apply ψ x := by
    congr 1; ext x; ring
  have hAeq : (∫ x, ψ x * A.apply φ x) = ∫ x, φ x * A.apply ψ x := by
    have := hA hψ.1 hφ.1
    unfold innerProduct at this
    rw [this, hcommA]
  have hBeq : (∫ x, ψ x * B.apply φ x) = ∫ x, φ x * B.apply ψ x := by
    have := hB hψ.2 hφ.2
    unfold innerProduct at this
    rw [this, hcommB]
  linarith

end DFT
