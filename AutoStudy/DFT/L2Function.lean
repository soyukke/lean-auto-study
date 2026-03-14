/-
  L² 関数と定義域付き作用素

  Basic.lean の bare ℝ → ℝ (1D toy model) に対して、
  二乗可積分性を明示的に束ねた L² 関数層を提供する。

  設計:
  - Basic.lean は bare 関数層 (1D toy model の簡略化された API)
  - L2Function.lean は L² 層 (二乗可積分性を型レベルで保証)
  - 相互変換 (L2Function.val, L2Function.ofNormalized) により
    既存の bare 関数層のコードと組み合わせて使用可能
-/
import AutoStudy.DFT.Basic

open MeasureTheory DFT

namespace DFT

/-- L² 関数の代表元。bare ℝ → ℝ に二乗可積分性を束ねる。
    MeasureTheory の a.e. 同値類とは異なり、具体的な代表元を保持する。
    a.e. 同値類が必要な場合は MeasureTheory.Lp を使用すること。 -/
structure L2Function where
  /-- 基礎となる bare 関数 -/
  val : ℝ → ℝ
  /-- 二乗可積分性: ∫ |f(x)|² dx < ∞ -/
  squareIntegrable : Integrable (fun x => val x * val x)

namespace L2Function

/-- 正規化された波動関数から L2Function を構成する。 -/
def ofNormalized (ψ : ℝ → ℝ) (hnorm : IsNormalized ψ) : L2Function where
  val := ψ
  squareIntegrable := hnorm.integrable

/-- L2Function の内積。 -/
noncomputable def inner (f g : L2Function) : ℝ :=
  innerProduct f.val g.val

/-- L2Function の電子密度。 -/
noncomputable def density (f : L2Function) : ℝ → ℝ :=
  electronDensity f.val

/-- L2Function の電子密度は非負。 -/
theorem density_nonneg (f : L2Function) (x : ℝ) :
    0 ≤ f.density x :=
  electronDensity_nonneg f.val x

/-- L2Function の電子密度は可積分。 -/
theorem density_integrable (f : L2Function) :
    Integrable f.density :=
  f.squareIntegrable

end L2Function

/-- 定義域付き線形作用素。Domain は作用素の定義域を指定する述語。
    unbounded 作用素 (運動エネルギー演算子等) の定義域を明示するために使用する。 -/
structure DomainOperator where
  /-- 作用素の定義域を指定する述語 -/
  domain : (ℝ → ℝ) → Prop
  /-- 定義域上の作用素 -/
  op : (ψ : ℝ → ℝ) → domain ψ → (ℝ → ℝ)

end DFT
