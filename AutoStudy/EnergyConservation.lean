/-
  1次元のエネルギー保存則

  ニュートンの運動方程式 m·a(t) = -V'(x(t)) のもとで、
  全エネルギー E(t) = (m/2)·v(t)² + V(x(t)) の時間微分が 0 であることを証明する。

  証明の概要:
    dE/dt = m·v(t)·a(t) + V'(x(t))·v(t)
          = v(t)·(m·a(t) + V'(x(t)))
          = v(t)·0    (∵ ニュートンの運動方程式)
          = 0
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

/-- 1次元のエネルギー保存則:
    保存力のもとでの運動では、運動エネルギー + ポテンシャルエネルギー は時間変化しない。 -/
theorem energy_conservation
    (x v a : ℝ → ℝ) (V dV : ℝ → ℝ) (m : ℝ)
    (hx : ∀ t, HasDerivAt x (v t) t)
    (hv : ∀ t, HasDerivAt v (a t) t)
    (hV : ∀ y, HasDerivAt V (dV y) y)
    (newton : ∀ t, m * a t = -(dV (x t))) :
    ∀ t, HasDerivAt (fun t => m / 2 * (v t * v t) + V (x t)) 0 t := by
  intro t
  -- v(t)·v(t) の微分 = a(t)·v(t) + v(t)·a(t)
  have hvv := (hv t).mul (hv t)
  -- (m/2)·v(t)² の微分 = (m/2)·(a(t)·v(t) + v(t)·a(t))
  have hkin := hvv.const_mul (m / 2)
  -- V(x(t)) の微分 = dV(x(t))·v(t)  [連鎖律]
  have hpot : HasDerivAt (V ∘ x) (dV (x t) * v t) t := by
    apply HasDerivAt.comp
    · exact hV (x t)
    · exact hx t
  -- 全エネルギーの微分を合わせる
  have htot : HasDerivAt (fun t => m / 2 * (v t * v t) + V (x t))
      (m / 2 * (a t * v t + v t * a t) + dV (x t) * v t) t := by
    have h := HasDerivAt.add hkin hpot
    convert h using 1
  -- ニュートンの運動方程式より微分値 = 0
  have h0 : m / 2 * (a t * v t + v t * a t) + dV (x t) * v t = 0 := by
    linear_combination v t * newton t
  rwa [h0] at htot
