/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
import Mathlib
import SpectralThm.toMathlib.Variation.Defs
import SpectralThm.toMathlib.Variation.Lemmas
import SpectralThm.ComplexMeasure.Integral

/-!
# Riesz–Markov–Kakutani representation theorem for complex linear functionals

This file contains the proof of the **Riesz Representations Theorem** a.k.a.
**Riesz–Markov–Kakutani theorem** (complex case).

## Main definition

* `ComplexRMK.rieszMeasure (Φ : C₀(X, ℂ) →L[ℂ] ℂ)` the `ComplexMeasure` associated to the linear
functional`Φ`.

## Main results

* `rieszMeasure_unique`: uniqueness of  `ComplexRMK.rieszMeasure`.
* `integral_rieszMeasure`: that integration with respect to `ComplexRMK.rieszMeasure` is equal to
the action of the linear functional.

## Overview

Firstly the uniqueness of measures satisfying the represenation equation is proven.

The proof of existence of such a measures takes advantage of the corresponding statement for ℝ-valued linear functionals and signed measures (see `Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`). As such, a major part of the argument is to reduce the complex situation to the case of a ℝ-valued linear functional. Moreover the required measure can be defined using the measure obtained in the ℝ-valued linear functional case.


## Notes

* File destination: `Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Complex.lean`

## References

* Section 6 of [Walter Rudin, Real and Complex Analysis.][Rud87]

## To do

- Rudin 6.16: Duality of `L^1` and `L^∞` (not in Mathlib [https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Lp.20duality/near/495207025])
-/

open NNReal ENNReal
open ZeroAtInfty MeasureTheory CompactlySupported CompactlySupportedContinuousMap

namespace ComplexRMK

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]

lemma eq_zero_of_integral_eq_zero {μ: ComplexMeasure X} (h : ∀ f : C₀(X, ℂ), μ.integral f = 0) :
    μ = 0 := by
  -- [Rudin 87, Theorem 6.19]
  -- Suppose `μ` is a regular complex Borel measure on `X`
  -- and that `∫ f dμ = 0` for all `f \in C_0(X)`.
  -- *Theorem 6.12* gives a Borel function `h`, such that `|h| = 1` and `dμ = h d|μ|`.
  -- For any sequence `{f_n}` in `C_0(X)` we then have
  -- `|μ|(X) = \int_X (\bar{h} - f_n) h`, `d|μ| ≤ \int_X |\bar{h} - f_n| \, d|μ|`.
  -- Since `C_c(X)` is dense in `L^1(|μ|)` (*Theorem 3.14*), `\{f_n\}` can be
  -- so chosen that the last expression in the above tends to 0 as `n → \infty`.
  -- Thus `|μ|(X) = 0`, and `μ = 0`.
  -- (Theorem 3.14: compactly supported continuous functions are dense in `L^p`,
  -- depends on 3.13 `MeasureTheory.Lp.simpleFunc.isDenseEmbedding`, this is written only for
  -- `NormalSpace α` and approximation given by bounded functions)
  -- It is easy to see that the difference of two regular complex Borel measures on `X` is regular.
  sorry

/-- Uniqueness of `ComplexRMK.rieszMeasure`: Let `Φ` be a linear functional on `C_0(X, ℂ)`. Suppose
that `μ`, `μ'` are complex Borel measures such that, `∀ f : C_0(X, ℂ)`, `Φ f = ∫ x, f x ∂μ` and
`Φ f = ∫ x, f x ∂μ'`. Then `μ = μ'`. -/
theorem rieszMeasure_unique {μ₁ μ₂ : ComplexMeasure X} (Φ : C₀(X, ℂ) →L[ℂ] ℂ)
    (h₁ : ∀ f : C₀(X, ℂ), μ₁.integral f = Φ f) (h₂ : ∀ f : C₀(X, ℂ), μ₂.integral f = Φ f):
    μ₁ = μ₂ := by
  let μ := μ₁ - μ₂
  suffices μ = 0 by exact eq_of_sub_eq_zero this
  refine eq_zero_of_integral_eq_zero (fun f ↦ ?_)
  calc μ.integral f
    _ = (μ₁ - μ₂).integral f := by rfl
    _ = μ₁.integral f - μ₂.integral f := by exact ComplexMeasure.integral_sub _ _ _
    _ = Φ f - Φ f := by rw [h₁, h₂]
    _ = 0 := by exact sub_self _

variable (Φ : C₀(X, ℂ) →L[ℂ] ℂ)

-- TO DO: define `norm` as a `ContinuousMap` and use `norm ∘ f` in the following instead of the
-- `absOfFunc X f` hack.
def absOfFunc₀ (f : C₀(X, ℂ)) : C₀(X, ℝ) := sorry
def absOfFunc_c (f : C_c(X, ℂ)) : C_c(X, ℝ) := sorry

-- TO DO: figure out using this coercial directly in the argument.
def toZeroAtInftyContinuousMap : C_c(X, ℂ) → C₀(X, ℂ) := fun f ↦ (f : C₀(X, ℂ))
def toZeroAtInftyContinuousMap' : C_c(X, ℝ) → C₀(X, ℝ) := fun f ↦ (f : C₀(X, ℝ))

noncomputable def identity : C_c(X, ℝ≥0) → C_c(X, ℝ) := CompactlySupportedContinuousMap.toReal

-- TO DO: define the identity between the ℝ and ℂ spaces of continuous functions,
-- similar to `CompactlySupportedContinuousMap.toReal`.
def toComplex : C_c(X, ℝ) → C_c(X, ℂ) := by sorry

/-- Let `Φ` be a bounded linear functional on `C₀(X, ℂ)`. There exists a positive linear functional
`Λ` on `C₀(X, ℝ)` such that, `∀ f : C₀(X, ℂ)`, `|Φ f| ≤ Λ |f|` and `Λ |f| ≤ ‖f‖` (`‖⬝‖` denotes
the supremum norm). [Rudin 87, part of proof of Theorem 6.19] -/
theorem exists_pos_lin_func : ∃ (Λ : C₀(X, ℝ) →L[ℝ] ℝ), ∀ (f : C₀(X, ℂ)),
    ‖Φ f‖ ≤ Λ (absOfFunc₀ f) ∧ Λ (absOfFunc₀ f) ≤ ‖f‖ := by

  -- If `f ∈` [class of all nonnegative real members of `C_c(X, ℝ)`],
  -- define `Λ f = \sup { |Φ(h)| : h ∈ C_c(X, ℂ), |h| ≤ f }`.
  let U (f : C_c(X, ℝ≥0)) := toZeroAtInftyContinuousMap '' {h : C_c(X, ℂ) | ∀ x : X, ‖h x‖ ≤ f x}
  let Λ' (f : C_c(X, ℝ≥0)) := sSup (norm '' (Φ '' U f))

  -- Then `Λ f ≥ 0`, `Λ` satisfies the two required inequalities,
  have (f : C_c(X, ℝ≥0)) : 0 ≤ Λ' f := by
    -- because it is the sup of nonnegative quantities
    unfold Λ'
    apply Real.sSup_nonneg
    intro x hx
    rw [Set.mem_image] at hx
    obtain ⟨a, _, ha⟩ := hx
    rw [← ha]
    positivity
  have (f : C_c(X, ℝ≥0)) : ‖Φ (toComplex (f.toReal))‖ ≤ Λ' f := by
    -- unfold Λ'
    -- apply le_csSup
    -- .
    --   rw [bddAbove_def]
    --   use ‖Φ (toComplex (f.toReal))‖
    --   intro y hy
    --   simp at hy
    --   obtain ⟨a, a_mem, ha⟩ := hy
    --   unfold U at a_mem
    --   simp at a_mem
    --   obtain ⟨g, hg, a_eq_g⟩ := a_mem
    --   rw [← a_eq_g] at ha
    --   rw [← ha]



    sorry
  have (f : C_c(X, ℝ≥0)) : Λ' f ≤ ‖toZeroAtInftyContinuousMap' f.toReal‖ := by
    sorry

  -- `0 ≤ f_1 ≤ f_2` implies `Λ f_1 ≤ Λ f_2`, and `Λ (cf) = c Λ f` if `c` is a positive constant.

  -- We have to show that
  -- (10) `Λ(f + g) = Λ f + Λ g` whenever `f, g ∈ C_c^+(X)`,
  -- and we then have to extend `Λ` to a linear functional on `C_c(X, ℝ)`.
  -- Fix `f` and `g \in C_c^+(X)`.
  -- If `ε > 0`, there exist `h_1, h_2 \in C_c(X, ℝ)` such that `|h_1| ≤ f`, `|h_2| ≤ g`,
  -- `Λ f ≤ |Φ(h_1)| + ε`, `Λ g ≤ |Φ(h_2)| + ε`.
  -- There are complex numbers `α_i`, `|α_i| = 1`, so that `α_i Φ(h_i) = |Φ(h_i)|`, `i = 1, 2`.
  -- Then
  -- `Λ f + Λ g ≤ |Φ(h_1)| + |Φ(h_2)| + 2ε`
  -- `_ = Φ(α_1 h_1 + α_2 h_2) + 2ε`
  -- `_ ≤ Λ(|h_1| + |h_2|) + 2ε`
  -- `_ ≤ Λ(f + g) + 2ε`
  -- so that the inequality `≥` holds in (10).
  -- Next, choose `h ∈ C_c(X)`, subject only to the condition `|h| ≤ f + g`,
  -- let `V = { x : f(x) + g(x) > 0 }`, and define
  -- `h_1(x) = \frac{f(x) h(x)}{f(x) + g(x)}`,
  -- `h_2(x) = \frac{g(x) h(x)}{f(x) + g(x)}` when `x ∈ V`,
  -- `h_1(x) = h_2(x) = 0` when `x ∉ V`.
  -- It is clear that `h_1` is continuous at every point of `V`.
  -- If `x_0 ∉ V`, then `h(x_0) = 0`;
  -- since `h` is continuous and since `|h_1(x)| ≤ |h(x)|` for all `x ∈ X`,
  -- it follows that `x_0` is a point of continuity of `h_1`.
  -- Thus `h_1 \in C_c(X)`, and the same holds for `h_2`.
  -- Since `h_1 + h_2 = h` and `|h_1| ≤ f`, `|h_2| ≤ g`, we have
  -- `|Φ(h)| = |Φ(h_1) + Φ(h_2)| ≤ |Φ(h_1)| + |Φ(h_2)| ≤ Λ f + Λ g`.
  -- Hence `Λ(f + g) ≤ Λ f + Λ g`, and we have proved (10).
  -- If `f` is now a real function, `f \in C_c(X)`, then `2f^+ = |f| + f`,
  -- so that `f^+ \in C_c^+(X)`;
  -- likewise, `f^- \in C_c^+(X)`; and since `f = f^+ - f^-`, it is natural to define
  -- `Λ f = Λ f^+ - Λ f^- ` for `f \in C_c(X)`, `f` real
  -- and
  -- `Λ(u + iv) = Λ u + i Λ v`.
  -- Simple algebraic manipulations, just like those which occur in the proof of
  -- Theorem 1.32, show now that our extended functional `Λ` is linear on `C_c(X)`.
  sorry

end ComplexRMK

namespace ComplexRMK

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
variable (Φ : C₀(X, ℂ) →L[ℂ] ℂ)
variable [MeasurableSpace X] [BorelSpace X]

/-- The measure induced by a `ℂ`-linear positive functional `Λ`. -/
noncomputable def rieszMeasure (Φ : C₀(X, ℂ) →L[ℂ] ℂ) : ComplexMeasure X :=
  -- To be defined according to the construction of the proof, using `RealRMK.rieszMeasure`.
  sorry

/-- **Theorem**
Let `Φ` be a bounded linear functional on `C₀(X, ℂ)`. Then there exists a complex Borel measure
`μ` such that, `∀ f : C₀(X, ℂ)`, `Φ f = ∫ x, f x ∂μ`, (2) `‖Φ‖ = |μ|(X)`. -/
theorem integral_rieszMeasure (f : C₀(X, ℂ)) :
     Φ f = (rieszMeasure Φ).integral (f ·) := by
  -- **Proof** [Rudin 87, Theorem 6.19]
  -- Assume `‖Φ‖ = 1`, without loss of generality.
  -- *Part 1:*
  -- Using `exists_pos_lin_func` we obtain a *positive* linear functional `Λ` on `C_c(X)`, such that
  -- (4) `|Φ(f)| ≤ Λ(|f|) ≤ ‖f‖` for all `f \in C_c(X))`.
  -- Once we have this `Λ`, we associate with it a positive Borel measure `λ`, given by
  -- have := RealRMK.integral_rieszMeasure
  -- `RealRMK.rieszMeasure hΛ` and which is a representation by `RealRMK.integral_rieszMeasure`.
  -- It also implies that `λ` is regular if `λ(X) < \infty`.
  -- Since `Λ(X) = \sup {Λ f : 0 ≤ f ≤ 1, f \in C_c(X)}`
  -- and since `|Λ f| ≤ 1` if `‖f‖ ≤ 1`, we see that actually `λ(X) ≤ 1`.
  -- We also deduce from (4) that
  -- `|Φ(f)| ≤ Λ(|f|) = ∫_X |f| dλ = ‖f‖_1`, `f \in C_c(X))`.
  -- The last norm refers to the space `L^1(λ)`.
  -- Thus `Φ` is a linear functional on `C_c(X)` of norm at most 1, with respect to the `L^1(λ)`-norm
  -- on `C_c(X)`.
  -- There is a norm-preserving extension of `Φ` to a linear functional on `L^1(λ)`, and therefore
  -- *Theorem 6.16* (the case `p = 1`) gives a Borel function `g`, with `|g| ≤ 1`, such that
  -- (6) `Φ(f) = ∫_X fg dλ`, `f \in C_c(X)`.
  -- Each side of (6) is a continuous functional on `C_0(X)`, and `C_c(X)` is dense in `C_0(X)`.
  -- Hence (6) holds for all `f \in C_0(X)`, and we obtain the representation with `dμ = g dλ`.
  -- *Part 2:*
  -- Since `\|Φ\| = 1`, (6) shows that
  -- `∫_X |g| dλ ≥ \sup { |Φ(f)| : f \in C_0(X), ‖f‖ ≤ 1 } = 1`.
  -- We also know that `λ(X) ≤ 1` and `|g| ≤ 1`.
  -- These facts are compatible only if `λ(X) = 1` and `|g| = 1` a.e. `[λ]`.
  -- Thus `d|μ| = |g| dλ = dλ`, by *Theorem 6.13*,
  -- and `|μ|(X) = λ(X) = 1 = ‖Φ‖`,
  sorry

theorem norm_eq_variation (f : C₀(X, ℂ)) :
    ENNReal.ofReal ‖Φ‖ = (rieszMeasure Φ).variation Set.univ := by
  sorry

end ComplexRMK


open ZeroAtInftyContinuousMap

namespace ZeroAtInftyContinuousMap

section NormedAddGroupHom

variable {α : Type*} {β : Type*} [TopologicalSpace α] [CompactSpace α]
  [SeminormedAddCommGroup β]

def ContinuousMap.liftZeroAtInftyNAGH : NormedAddGroupHom C(α, β) C₀(α, β) where
  toFun := ContinuousMap.liftZeroAtInfty
  map_add' x y := rfl
  bound' := ⟨1, by intro v; simp; apply le_of_eq; rfl⟩

@[simp]
lemma liftZeroAtInftyNAGH_apply (f : C(α, β)) : f.liftZeroAtInftyNAGH = f.liftZeroAtInfty := rfl

end NormedAddGroupHom

section ContinuousLinearEquiv

variable {α : Type*} {β : Type*} {R : Type*} [TopologicalSpace α] [CompactSpace α]
  [SeminormedAddCommGroup β] [Semiring R] [Module R β] [ContinuousConstSMul R β]

noncomputable def ContinuousMap.liftZeroAtInftyCLE : C(α, β) ≃L[R] C₀(α, β) :=
  { toFun := ContinuousMap.liftZeroAtInftyNAGH
    map_add' x y := rfl
    map_smul' c x := rfl
    invFun f := f
    continuous_invFun := Isometry.continuous fun _ ↦ congrFun rfl
  }

end ContinuousLinearEquiv
