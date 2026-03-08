/-
  交換相関汎関数の構造

  DFT における中心的な未知量 E_xc[ρ] の構造を定義する。
  E_xc = E_x + E_c（交換エネルギー + 相関エネルギー）への分解と、
  局所汎関数・半局所汎関数の一般的な形式を定義する。
-/
import AutoStudy.DFT.Basic

open MeasureTheory DFT

noncomputable section

namespace DFT

/-- 交換相関汎関数: E_xc = E_x + E_c -/
structure XCFunctional where
  /-- 交換相関エネルギー E_xc[ρ] -/
  E_xc : (ℝ → ℝ) → ℝ
  /-- 交換エネルギー E_x[ρ] -/
  E_x : (ℝ → ℝ) → ℝ
  /-- 相関エネルギー E_c[ρ] -/
  E_c : (ℝ → ℝ) → ℝ
  /-- 分解条件: E_xc[ρ] = E_x[ρ] + E_c[ρ] -/
  decomposition : ∀ ρ, E_xc ρ = E_x ρ + E_c ρ

namespace XCFunctional

variable (xc : XCFunctional)

/-- 交換・相関が共に非正ならば E_xc も非正 -/
theorem xc_nonpositive_of_components
    (hx : ∀ ρ, xc.E_x ρ ≤ 0) (hc : ∀ ρ, xc.E_c ρ ≤ 0) (ρ : ℝ → ℝ) :
    xc.E_xc ρ ≤ 0 := by
  rw [xc.decomposition]
  exact add_nonpos (hx ρ) (hc ρ)

/-- E_xc の差分は E_x と E_c の差分の和 -/
theorem xc_diff (ρ₁ ρ₂ : ℝ → ℝ) :
    xc.E_xc ρ₁ - xc.E_xc ρ₂ =
    (xc.E_x ρ₁ - xc.E_x ρ₂) + (xc.E_c ρ₁ - xc.E_c ρ₂) := by
  rw [xc.decomposition ρ₁, xc.decomposition ρ₂]; ring

/-- E_xc の下界: E_x ≥ bx かつ E_c ≥ bc ならば E_xc ≥ bx + bc -/
theorem xc_lower_bound {bx bc : ℝ}
    (hx : ∀ ρ, bx ≤ xc.E_x ρ) (hc : ∀ ρ, bc ≤ xc.E_c ρ) (ρ : ℝ → ℝ) :
    bx + bc ≤ xc.E_xc ρ := by
  rw [xc.decomposition]
  exact add_le_add (hx ρ) (hc ρ)

end XCFunctional

/-- 局所汎関数のエネルギー: E[ρ] = ∫ f(ρ(x)) dx
    LDA 型の汎関数はこの形をとる -/
def localFunctionalEnergy (f : ℝ → ℝ) (ρ : ℝ → ℝ) : ℝ :=
  ∫ x, f (ρ x)

/-- 重み付き局所汎関数: E[ρ] = ∫ ρ(x) · ε(ρ(x)) dx
    ε(ρ) は1粒子あたりのエネルギー密度 -/
def weightedLocalEnergy (ε : ℝ → ℝ) (ρ : ℝ → ℝ) : ℝ :=
  ∫ x, ρ x * ε (ρ x)

/-- 半局所汎関数のエネルギー: E[ρ, ∇ρ] = ∫ f(ρ(x), |∇ρ(x)|) dx
    GGA 型の汎関数はこの形をとる -/
def semiLocalFunctionalEnergy (f : ℝ → ℝ → ℝ) (ρ gradρ : ℝ → ℝ) : ℝ :=
  ∫ x, f (ρ x) (gradρ x)

end DFT
