import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.Obj
import OAI.AlgebraicGeometry.DivisorClass.Chern.Logarithms

/-! # Log Cech -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.LogCech

noncomputable section

section

/-!
# ChernClass: rational singular classes of continuous logarithmic transition data

The inputs are continuous logarithms on pairwise cover intersections whose
exponentials satisfy the multiplicative cocycle identity. Their actual
logarithmic defects give a locally constant rational Cech cocycle and hence
a class in the existing rational singular cohomology.

This module does not assume a Chern class, a divisor compatibility statement,
or the Lefschetz theorem. Producing this cover data from every algebraic line
bundle, and comparing it to the divisor-class construction, are separate steps.
-/

open _root_.CategoryTheory Opposite _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.Logarithms.Construction
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech

/-- Continuous complex functions, as a presheaf of rational vector spaces. -/
abbrev continuousComplexPresheaf (X : TopCat.{0}) : X.Presheaf (ModuleCat.{0} ℚ) where
  obj U := ModuleCat.of ℚ C(U.unop, ℂ)
  map i := ModuleCat.ofHom {
    toFun := fun f => f.comp ⟨i.unop, (Opens.isOpenEmbedding_of_le i.unop.le).continuous⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  map_id _ := by ext f x; rfl
  map_comp _ _ := by ext f x; rfl

/-- Multiplication of a rational local constant by the exponential period 2πi. -/
def periodMap (X : TopCat.{0}) :
    Cech.Obj.RationalCech.locallyConstantPresheaf X ⟶ continuousComplexPresheaf X where
  app U := ModuleCat.ofHom {
    toFun := fun c => {
      toFun := fun x => (c x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
      continuous_toFun := (c.isLocallyConstant.comp
        (fun q : ℚ => (q : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))).continuous }
    map_add' := by
      intro c d
      ext x
      change ((c x + d x : ℚ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
        (c x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
          (d x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
      push_cast
      ring
    map_smul' := by
      intro q c
      ext x
      change ((q * c x : ℚ) : ℂ) * _ = (q : ℂ) * ((c x : ℂ) * _)
      push_cast
      ring }
  naturality _ _ _ := by ext c; rfl

theorem periodMap_injective (X : TopCat.{0}) (U : Opens X) :
    Function.Injective ((periodMap X).app (op U)) := by
  intro c d h
  apply LocallyConstant.ext
  intro x
  have he := congrArg (fun f : C(U, ℂ) => f x) h
  change (c x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
    (d x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) at he
  have hc := mul_right_cancel₀ Complex.two_pi_I_ne_zero he
  exact_mod_cast hc

variable {ι : Type} (X : TopCat.{0}) (U : ι → Opens X)

theorem periodCechMap_injective (n : ℕ) :
    Function.Injective (Rational.Cech.RationalCech.cechCoefficientMap U (periodMap X) n) := by
  intro c d h
  funext a
  exact periodMap_injective X _ (congrFun h a)

/-- Continuous logarithms on each ordered pairwise intersection. -/
abbrev LogCechCochain := Rational.Cech.RationalCech.CechCochain (continuousComplexPresheaf X) U 1

/-- Restrict the indicated edge logarithm to a triple intersection. -/
abbrev edgeLog (l : LogCechCochain X U) (j : Fin 3) :
    Rational.Cech.RationalCech.CechCochain (continuousComplexPresheaf X) U 2 :=
  Rational.Cech.RationalCech.cechPrecomp (continuousComplexPresheaf X) U j.succAbove l

/-- The exponentials of the supplied logarithms form a transition cocycle. -/
def ExponentialCocycle (l : LogCechCochain X U) : Prop :=
  ∀ (a : Fin 3 → ι) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
    Complex.exp (edgeLog X U l 2 a x) * Complex.exp (edgeLog X U l 0 a x) =
      Complex.exp (edgeLog X U l 1 a x)

/-- Rationalized integral logarithmic defects on triple intersections. -/
def logDefectCech (l : LogCechCochain X U) (h : ExponentialCocycle X U l) :
    Rational.Cech.RationalCech.CechCochain (Cech.Obj.RationalCech.locallyConstantPresheaf X) U 2 :=
  fun a => {
    toFun := fun x => (Logarithms.Construction.logarithmicDefect
      (edgeLog X U l 2 a x) (edgeLog X U l 0 a x) (edgeLog X U l 1 a x) (h a x) : ℚ)
    isLocallyConstant := (Logarithms.Construction.isLocallyConstant_logarithmicDefect
      (edgeLog X U l 2 a) (edgeLog X U l 0 a) (edgeLog X U l 1 a) (h a)).comp
        (fun n : ℤ => (n : ℚ)) }

/-- The rational defect is exactly the Cech coboundary of the logarithms divided by 2πi. -/
theorem periodMap_logDefectCech (l : LogCechCochain X U)
    (h : ExponentialCocycle X U l) :
    Rational.Cech.RationalCech.cechCoefficientMap U (periodMap X) 2 (logDefectCech X U l h) =
      Rational.Cech.RationalCech.cechDelta (continuousComplexPresheaf X) U 1 l := by
  funext a
  apply ContinuousMap.ext
  intro x
  have hd := Logarithms.Construction.logarithmicDefect_spec
    (edgeLog X U l 2 a x) (edgeLog X U l 0 a x) (edgeLog X U l 1 a x) (h a x)
  change (((Logarithms.Construction.logarithmicDefect _ _ _ (h a x) : ℤ) : ℚ) : ℂ) * _ = _
  push_cast
  rw [← hd, Rational.Cech.RationalCech.cechDelta_apply, Fin.sum_univ_three]
  change edgeLog X U l 2 a x + edgeLog X U l 0 a x - edgeLog X U l 1 a x =
    (1 : ℤ) • edgeLog X U l 0 a x + (-1 : ℤ) • edgeLog X U l 1 a x +
      (1 : ℤ) • edgeLog X U l 2 a x
  simp only [one_zsmul, neg_one_zsmul]
  ring

/-- Closedness follows from the actual Cech differential squared being zero. -/
theorem logDefectCech_closed (l : LogCechCochain X U)
    (h : ExponentialCocycle X U l) :
    Rational.Cech.RationalCech.cechDelta (Cech.Obj.RationalCech.locallyConstantPresheaf X) U 2 (logDefectCech X U l h) = 0 := by
  apply periodCechMap_injective X U 3
  rw [map_zero, Rational.Cech.RationalCech.cechCoefficientMap_delta, periodMap_logDefectCech, Rational.Cech.RationalCech.cechDelta_squared]

/-- The actual logarithmic defect as a cocycle of the rational Cech complex. -/
def logDefectCocycle (l : LogCechCochain X U) (h : ExponentialCocycle X U l) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Rational.Cech.RationalCech.cechComplex (Cech.Obj.RationalCech.locallyConstantPresheaf X) U) 2 :=
  ⟨logDefectCech X U l h, by
    rw [AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff, Rational.Cech.RationalCech.cechComplex_d]
    exact logDefectCech_closed X U l h⟩

/-- The rational singular cohomology class obtained from logarithmic transition data. -/
def logarithmicSingularClass (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (l : LogCechCochain X U) (h : ExponentialCocycle X U l) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X 2 :=
  Cech.Obj.RationalCech.singularClassOfCechCocycle X U hcover 2 (logDefectCocycle X U l h)

/-- Two logarithms of the same transition differ by a locally constant integer period. -/
def logDifferenceCech (l l' : LogCechCochain X U)
    (he : ∀ (a : Fin 2 → ι) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l a x) = Complex.exp (l' a x)) :
    Rational.Cech.RationalCech.CechCochain (Cech.Obj.RationalCech.locallyConstantPresheaf X) U 1 :=
  fun a => {
    toFun := fun x => (Logarithms.Construction.logarithmicDefect (l a x) 0 (l' a x)
      (by simpa only [Complex.exp_zero, mul_one] using he a x) : ℚ)
    isLocallyConstant := (Logarithms.Construction.isLocallyConstant_logarithmicDefect
      (l a) 0 (l' a) (fun x => by
        simpa only [ContinuousMap.zero_apply, Complex.exp_zero, mul_one] using he a x)).comp
      (fun n : ℤ => (n : ℚ)) }

theorem periodMap_logDifferenceCech (l l' : LogCechCochain X U)
    (he : ∀ (a : Fin 2 → ι) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l a x) = Complex.exp (l' a x)) :
    Rational.Cech.RationalCech.cechCoefficientMap U (periodMap X) 1 (logDifferenceCech X U l l' he) = l - l' := by
  funext a
  apply ContinuousMap.ext
  intro x
  have h := Logarithms.Construction.logarithmicDefect_spec (l a x) 0 (l' a x)
    (by simpa only [Complex.exp_zero, mul_one] using he a x)
  change (((Logarithms.Construction.logarithmicDefect _ _ _ _ : ℤ) : ℚ) : ℂ) * _ = l a x - l' a x
  push_cast
  simpa only [add_zero] using h.symm

/-- Changing logarithms changes the actual defect cocycle by an actual Cech coboundary. -/
theorem logDefectCech_sub_is_boundary (l l' : LogCechCochain X U)
    (h : ExponentialCocycle X U l) (h' : ExponentialCocycle X U l')
    (he : ∀ (a : Fin 2 → ι) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l a x) = Complex.exp (l' a x)) :
    Rational.Cech.RationalCech.cechDelta (Cech.Obj.RationalCech.locallyConstantPresheaf X) U 1 (logDifferenceCech X U l l' he) =
      logDefectCech X U l h - logDefectCech X U l' h' := by
  apply periodCechMap_injective X U 2
  rw [Rational.Cech.RationalCech.cechCoefficientMap_delta, periodMap_logDifferenceCech, map_sub, map_sub,
    periodMap_logDefectCech, periodMap_logDefectCech]

/-- The rational singular class is independent of the choice of continuous logarithms
 on a fixed cover for the same exponential transition functions. -/
theorem logarithmicSingularClass_log_independent
    (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (l l' : LogCechCochain X U)
    (h : ExponentialCocycle X U l) (h' : ExponentialCocycle X U l')
    (he : ∀ (a : Fin 2 → ι) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l a x) = Complex.exp (l' a x)) :
    logarithmicSingularClass X U hcover l h =
      logarithmicSingularClass X U hcover l' h' := by
  apply Cech.Obj.RationalCech.singularClassOfCechCocycle_eq_of_boundary X U hcover 1
    (logDefectCocycle X U l h) (logDefectCocycle X U l' h')
    (logDifferenceCech X U l l' he)
  exact logDefectCech_sub_is_boundary X U l l' h h' he

end RationalCech

end

/-! Negating actual logarithms negates their original rational singular class. -/

open _root_.CategoryTheory _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech
variable {ι : Type} (X : TopCat.{0}) (U : ι → Opens X)

theorem exponentialCocycle_neg (l : LogCechCochain X U) (h : ExponentialCocycle X U l) :
    ExponentialCocycle X U (-l) := by
  intro a x
  change Complex.exp (-edgeLog X U l 2 a x) * Complex.exp (-edgeLog X U l 0 a x) =
    Complex.exp (-edgeLog X U l 1 a x)
  rw [Complex.exp_neg, Complex.exp_neg, Complex.exp_neg, ← mul_inv, h a x]

theorem logDefectCech_neg (l : LogCechCochain X U) (h : ExponentialCocycle X U l) :
    logDefectCech X U (-l) (exponentialCocycle_neg X U l h) = -logDefectCech X U l h := by
  apply periodCechMap_injective X U 2
  rw [periodMap_logDefectCech, map_neg, map_neg, periodMap_logDefectCech]

theorem logDefectCocycle_neg (l : LogCechCochain X U) (h : ExponentialCocycle X U l) :
    logDefectCocycle X U (-l) (exponentialCocycle_neg X U l h) = -logDefectCocycle X U l h := by
  apply Subtype.ext
  exact logDefectCech_neg X U l h

theorem logarithmicSingularClass_neg (hU : ∀ x : X, ∃ i, x ∈ U i)
    (l : LogCechCochain X U) (h : ExponentialCocycle X U l) :
    logarithmicSingularClass X U hU (-l) (exponentialCocycle_neg X U l h) =
      -logarithmicSingularClass X U hU l h := by
  unfold logarithmicSingularClass
  rw [logDefectCocycle_neg X U l h]
  simp only [Cech.Obj.RationalCech.singularClassOfCechCocycle, map_neg]

end RationalCech

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.LogCech
