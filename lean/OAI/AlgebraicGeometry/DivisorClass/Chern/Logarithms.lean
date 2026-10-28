import OAI.AlgebraicGeometry.DivisorClass.Chern.AnalyticTransitions
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Tactic.Ring

/-! # Logarithms -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-!
# ChernClass: local logarithms and integral logarithmic defects

Nonvanishing continuous transition functions admit continuous logarithms
on explicitly constructed neighborhoods. The multiplicative transition
identity makes the additive logarithmic defect an integral multiple of
2πi. These integers satisfy the degree-two cocycle identity.

This is local construction data. No identification with singular cohomology
or with the geometric divisor-class map is asserted here.
-/

open _root_.Topology

namespace Logarithms.Construction

variable {T : Type*} [TopologicalSpace T]

/-- Rotate and rescale the logarithm's slit plane to the value at the chosen point. -/
def logarithmNeighborhood (g : C(T, ℂ)) (p : T) : Set T :=
  {q | g q / g p ∈ Complex.slitPlane}

theorem isOpen_logarithmNeighborhood (g : C(T, ℂ)) (p : T) :
    IsOpen (logarithmNeighborhood g p) :=
  Complex.isOpen_slitPlane.preimage (g.continuous.div_const (g p))

theorem mem_logarithmNeighborhood (g : C(T, ℂ)) (p : T) (hp : g p ≠ 0) :
    p ∈ logarithmNeighborhood g p := by
  simpa only [logarithmNeighborhood, Set.mem_ofPred_eq, div_self hp] using
    Complex.one_mem_slitPlane

/-- A continuous logarithm on this explicit neighborhood. -/
def localLogarithm (g : C(T, ℂ)) (p : T) :
    C(logarithmNeighborhood g p, ℂ) where
  toFun q := Complex.log (g q / g p) + Complex.log (g p)
  continuous_toFun :=
    (((g.continuous.comp continuous_subtype_val).div_const (g p)).clog
      (fun q => q.property)).add continuous_const

theorem exp_localLogarithm (g : C(T, ℂ)) (p : T) (hp : g p ≠ 0)
    (q : logarithmNeighborhood g p) :
    Complex.exp (localLogarithm g p q) = g q := by
  change Complex.exp (Complex.log (g q / g p) + Complex.log (g p)) = g q
  rw [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero q.property),
    Complex.exp_log hp, div_mul_cancel₀ _ hp]

/-- A multiplicative transition relation forces the log defect into 2πiℤ. -/
theorem exists_logarithmicDefect (a b c : ℂ)
    (h : Complex.exp a * Complex.exp b = Complex.exp c) :
    ∃ n : ℤ, a + b - c = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  apply Complex.exp_eq_one_iff.mp
  rw [Complex.exp_sub, Complex.exp_add, h, div_self (Complex.exp_ne_zero c)]

/-- The integer is extracted from the actual logarithms and their exponential relation. -/
def logarithmicDefect (a b c : ℂ)
    (h : Complex.exp a * Complex.exp b = Complex.exp c) : ℤ :=
  (exists_logarithmicDefect a b c h).choose

theorem logarithmicDefect_spec (a b c : ℂ)
    (h : Complex.exp a * Complex.exp b = Complex.exp c) :
    a + b - c = (logarithmicDefect a b c h : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I) :=
  (exists_logarithmicDefect a b c h).choose_spec

/-- The choice of an integer witness introduces no ambiguity. -/
theorem logarithmicDefect_unique (a b c : ℂ)
    (h : Complex.exp a * Complex.exp b = Complex.exp c) (n : ℤ)
    (hn : a + b - c = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) :
    n = logarithmicDefect a b c h := by
  have he : (n : ℂ) = (logarithmicDefect a b c h : ℂ) :=
    mul_right_cancel₀ Complex.two_pi_I_ne_zero
      (hn.symm.trans (logarithmicDefect_spec a b c h))
  exact_mod_cast he

/-- Continuous local logarithms give a continuous integer-valued defect. -/
theorem continuous_logarithmicDefect (a b c : C(T, ℂ))
    (h : ∀ p, Complex.exp (a p) * Complex.exp (b p) = Complex.exp (c p)) :
    Continuous (fun p => logarithmicDefect (a p) (b p) (c p) (h p)) := by
  apply Complex.isClosedEmbedding_intCast.isEmbedding.isInducing.continuous_iff.mpr
  have he : (fun p => (logarithmicDefect (a p) (b p) (c p) (h p) : ℂ)) =
      (fun p => (a p + b p - c p) / (2 * (Real.pi : ℂ) * Complex.I)) := by
    funext p
    apply (eq_div_iff Complex.two_pi_I_ne_zero).mpr
    exact (logarithmicDefect_spec (a p) (b p) (c p) (h p)).symm
  change Continuous (fun p => (logarithmicDefect (a p) (b p) (c p) (h p) : ℂ))
  rw [he]
  exact ((a.continuous.add b.continuous).sub c.continuous).div_const _

/-- The integer defect is locally constant, as required for integral coefficients. -/
theorem isLocallyConstant_logarithmicDefect (a b c : C(T, ℂ))
    (h : ∀ p, Complex.exp (a p) * Complex.exp (b p) = Complex.exp (c p)) :
    IsLocallyConstant (fun p => logarithmicDefect (a p) (b p) (c p) (h p)) :=
  (IsLocallyConstant.iff_continuous _).mpr (continuous_logarithmicDefect a b c h)

/-- On a quadruple overlap, the alternating sum of the four defects vanishes. -/
theorem logarithmicDefect_cocycle
    (a01 a02 a03 a12 a13 a23 : ℂ)
    (h012 : Complex.exp a01 * Complex.exp a12 = Complex.exp a02)
    (h013 : Complex.exp a01 * Complex.exp a13 = Complex.exp a03)
    (h023 : Complex.exp a02 * Complex.exp a23 = Complex.exp a03)
    (h123 : Complex.exp a12 * Complex.exp a23 = Complex.exp a13) :
    logarithmicDefect a12 a23 a13 h123 - logarithmicDefect a02 a23 a03 h023 +
      logarithmicDefect a01 a13 a03 h013 - logarithmicDefect a01 a12 a02 h012 = 0 := by
  have he : ((logarithmicDefect a12 a23 a13 h123 : ℂ) -
      (logarithmicDefect a02 a23 a03 h023 : ℂ) +
      (logarithmicDefect a01 a13 a03 h013 : ℂ) -
      (logarithmicDefect a01 a12 a02 h012 : ℂ)) *
      (2 * (Real.pi : ℂ) * Complex.I) = 0 := by
    rw [sub_mul, add_mul, sub_mul, ← logarithmicDefect_spec,
      ← logarithmicDefect_spec, ← logarithmicDefect_spec, ← logarithmicDefect_spec]
    ring
  have hz := (mul_eq_zero.mp he).resolve_right Complex.two_pi_I_ne_zero
  exact_mod_cast hz

end Logarithms.Construction

/-- Every actual algebraic transition admits a continuous logarithm near each
 complex point of the overlap. -/
theorem Line.Bundles.AlgebraicLineBundle.exists_localLogarithm {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (L : Line.Bundles.AlgebraicLineBundle X) (x y : X.carrier) (W : X.carrier.Opens)
    (hx : W ≤ L.trivializingOpen x) (hy : W ≤ L.trivializingOpen y)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Line.Bundles.AlgebraicLineBundle.openOver W)) :
    ∃ U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Line.Bundles.AlgebraicLineBundle.openOver W)), IsOpen U ∧ p ∈ U ∧
      ∃ l : C(U, ℂ), ∀ q : U, Complex.exp (l q) = L.analyticTransitionOn x y W hx hy q := by
  let g := L.analyticTransitionOn x y W hx hy
  have hp : g p ≠ 0 := L.analyticTransitionOn_ne_zero x y W hx hy p
  exact ⟨Logarithms.Construction.logarithmNeighborhood g p, Logarithms.Construction.isOpen_logarithmNeighborhood g p,
    Logarithms.Construction.mem_logarithmNeighborhood g p hp, Logarithms.Construction.localLogarithm g p,
    fun q => Logarithms.Construction.exp_localLogarithm g p hp q⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
