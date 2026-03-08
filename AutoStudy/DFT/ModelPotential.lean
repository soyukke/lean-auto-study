/-
  モデルポテンシャル

  エネルギー汎関数 E_xc[ρ] から汎関数微分 v_xc = δE_xc/δρ で得られる
  ポテンシャルとは異なり、v_xc(r) を直接定義するアプローチ。

  LB94, SAOP, BJ 等の漸近補正ポテンシャルはこのカテゴリに属する。
  これらは正しい -1/r 漸近挙動を持つが、対応するエネルギー汎関数が
  一般に存在しない。

  XCFunctional (エネルギーベース) との根本的な違い:
    - XCFunctional: E_xc[ρ] を定義 → v_xc = δE_xc/δρ で導出
    - ModelPotential: v_xc[ρ](r) を直接定義（E_xc は不要/不在）
-/
import AutoStudy.DFT.ExchangeCorrelation
import AutoStudy.DFT.ExactConstraints
import AutoStudy.DFT.ExactConstraints.Asymptotic

open MeasureTheory DFT Filter

noncomputable section

namespace DFT

/-- モデルポテンシャル: v_xc(r) を密度と密度勾配から直接定義する。
    エネルギー汎関数を経由せず、ポテンシャルそのものが基本的な量。 -/
structure ModelPotential where
  /-- 交換相関ポテンシャル v_xc[ρ, ∇ρ](r) -/
  v_xc : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ)

namespace ModelPotential

variable (mp : ModelPotential)

/-- ポテンシャルの非正性 -/
def IsNonPositive : Prop :=
  ∀ ρ gradρ, (∀ x, 0 ≤ ρ x) → ∀ r, mp.v_xc ρ gradρ r ≤ 0

/-- 均一密度極限: ∇ρ = 0 のとき局所ポテンシャルに帰着 -/
def ReducesToLocal (v_local : ℝ → ℝ) : Prop :=
  ∀ ρ, mp.v_xc ρ (fun _ => 0) = fun r => v_local (ρ r)

/-- 正しい漸近減衰: 物理的密度に対して r * v_xc(r) → -1 -/
def HasAsymptoticDecay : Prop :=
  ∀ ρ gradρ, (∀ x, 0 ≤ ρ x) →
    HasCorrectAsymptoticDecay (mp.v_xc ρ gradρ)

end ModelPotential

end DFT
