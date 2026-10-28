import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicGeometry.DivisorClass.Chern.SimplexLogarithms
import OAI.AlgebraicTopology.Cohomology.Singular.Augmentation
import OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality

/-! # Winding Singular -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.WindingSingular

noncomputable section

section

/-!
# ChernClass: winding on genuine singular paths

A logarithm lifted along a singular path has a well-defined increment.
Subtracting the principal endpoint logarithms gives an actual integer period.
The resulting rational singular cochain is closed, proved using a continuous
logarithm on each singular triangle. No winding normalization is assumed.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped Simplicial

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : TopCat.{0}) (g : C(X, ℂ)) (hg : ∀ x, g x ≠ 0)

/-- Restriction of the function to an actual singular simplex. -/
def simplexFunction {n : ℕ} (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), ℂ) :=
  g.comp (X.toSSetObjEquiv _ s)

def singularSimplexLog {n : ℕ} (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), ℂ) :=
  SimplexLogarithms.simplexLogarithm n (simplexFunction X g s) (fun x => hg (X.toSSetObjEquiv _ s x))

theorem singularSimplexLog_exp {n : ℕ} (s : (TopCat.toSSet.obj X) _⦋n⦌)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    Complex.exp (singularSimplexLog X g hg s x) = simplexFunction X g s x :=
  SimplexLogarithms.exp_simplexLogarithm n _ _ x

/-- The actual increment of a lifted logarithm from the first vertex to the last. -/
def singularLogIncrement (s : (TopCat.toSSet.obj X) _⦋1⦌) : ℂ :=
  singularSimplexLog X g hg s (Convexity.StdSimplex.single 1) -
    singularSimplexLog X g hg s (Convexity.StdSimplex.single 0)

theorem singularLogIncrement_of_log (s : (TopCat.toSSet.obj X) _⦋1⦌)
    (l : C(Convexity.StdSimplex ℝ (Fin 2), ℂ))
    (hl : ∀ x, Complex.exp (l x) = simplexFunction X g s x) :
    singularLogIncrement X g hg s = l (Convexity.StdSimplex.single 1) - l (Convexity.StdSimplex.single 0) :=
  SimplexLogarithms.logarithm_increment_independent (singularSimplexLog X g hg s) l
    (fun x => (singularSimplexLog_exp X g hg s x).trans (hl x).symm) _ _

theorem singularLogIncrement_exp (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    Complex.exp (singularLogIncrement X g hg s) =
      simplexFunction X g s (Convexity.StdSimplex.single 1) /
        simplexFunction X g s (Convexity.StdSimplex.single 0) := by
  rw [singularLogIncrement, Complex.exp_sub, singularSimplexLog_exp, singularSimplexLog_exp]

theorem singularLogIncrement_period (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    Complex.exp (singularLogIncrement X g hg s) *
      Complex.exp (Complex.log (simplexFunction X g s (Convexity.StdSimplex.single 0))) =
    Complex.exp (Complex.log (simplexFunction X g s (Convexity.StdSimplex.single 1))) := by
  rw [singularLogIncrement_exp]
  change _ / _ * Complex.exp (Complex.log (g _)) = Complex.exp (Complex.log (g _))
  rw [Complex.exp_log (hg _), Complex.exp_log (hg _)]
  exact div_mul_cancel₀ _ (hg _)

/-- The integer winding contribution of one singular path, rationalized. -/
def singularWindingValue (s : (TopCat.toSSet.obj X) _⦋1⦌) : ℚ :=
  Logarithms.Construction.logarithmicDefect (singularLogIncrement X g hg s)
    (Complex.log (simplexFunction X g s (Convexity.StdSimplex.single 0)))
    (Complex.log (simplexFunction X g s (Convexity.StdSimplex.single 1)))
    (singularLogIncrement_period X g hg s)

/-- Recover the actual lifted increment from its rationalized integer period. -/
theorem singularWindingValue_period (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    (singularWindingValue X g hg s : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
      singularLogIncrement X g hg s +
        Complex.log (simplexFunction X g s (Convexity.StdSimplex.single 0)) -
        Complex.log (simplexFunction X g s (Convexity.StdSimplex.single 1)) := by
  unfold singularWindingValue
  push_cast
  exact (Logarithms.Construction.logarithmicDefect_spec _ _ _ (singularLogIncrement_period X g hg s)).symm

/-- One logarithm on a singular triangle computes every edge increment. -/
theorem singularLogIncrement_face (s : (TopCat.toSSet.obj X) _⦋2⦌) (i : Fin 3) :
    singularLogIncrement X g hg ((TopCat.toSSet.obj X).δ i s) =
      singularSimplexLog X g hg s (Convexity.StdSimplex.single (i.succAbove 1)) -
        singularSimplexLog X g hg s (Convexity.StdSimplex.single (i.succAbove 0)) := by
  let l := (singularSimplexLog X g hg s).comp
    ⟨Convexity.StdSimplex.map i.succAbove, Convexity.StdSimplex.continuous_map ℝ i.succAbove⟩
  have hl : ∀ x, Complex.exp (l x) =
      simplexFunction X g ((TopCat.toSSet.obj X).δ i s) x := by
    intro x
    exact singularSimplexLog_exp X g hg s _
  rw [singularLogIncrement_of_log X g hg _ l hl]
  simp only [l, ContinuousMap.comp_apply, ContinuousMap.coe_mk, Convexity.StdSimplex.map_single]

/-- The integer periods sum to zero around every actual singular triangle. -/
theorem singularWindingValue_triangle (s : (TopCat.toSSet.obj X) _⦋2⦌) :
    singularWindingValue X g hg ((TopCat.toSSet.obj X).δ 0 s) -
        singularWindingValue X g hg ((TopCat.toSSet.obj X).δ 1 s) +
      singularWindingValue X g hg ((TopCat.toSSet.obj X).δ 2 s) = 0 := by
  apply (Rat.cast_injective (α := ℂ))
  apply mul_right_cancel₀ Complex.two_pi_I_ne_zero
  push_cast
  rw [add_mul, sub_mul, singularWindingValue_period, singularWindingValue_period,
    singularWindingValue_period, singularLogIncrement_face, singularLogIncrement_face,
    singularLogIncrement_face]
  simp only [simplexFunction, ContinuousMap.comp_apply, TopCat.toSSetObjEquiv_δ_apply,
    Convexity.StdSimplex.map_single]
  change (singularSimplexLog X g hg s (Convexity.StdSimplex.single 2) -
      singularSimplexLog X g hg s (Convexity.StdSimplex.single 1) +
      Complex.log (g (X.toSSetObjEquiv _ s (Convexity.StdSimplex.single 1))) -
      Complex.log (g (X.toSSetObjEquiv _ s (Convexity.StdSimplex.single 2)))) -
    (singularSimplexLog X g hg s (Convexity.StdSimplex.single 2) -
      singularSimplexLog X g hg s (Convexity.StdSimplex.single 0) +
      Complex.log (g (X.toSSetObjEquiv _ s (Convexity.StdSimplex.single 0))) -
      Complex.log (g (X.toSSetObjEquiv _ s (Convexity.StdSimplex.single 2)))) +
    (singularSimplexLog X g hg s (Convexity.StdSimplex.single 1) -
      singularSimplexLog X g hg s (Convexity.StdSimplex.single 0) +
      Complex.log (g (X.toSSetObjEquiv _ s (Convexity.StdSimplex.single 0))) -
      Complex.log (g (X.toSSetObjEquiv _ s (Convexity.StdSimplex.single 1)))) = 0 * _
  ring

/-- The cochain is defined on every genuine singular path. -/
def singularWindingCochain : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X 1 :=
  (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) 1).inv
    (singularWindingValue X g hg)

theorem singularWindingCochain_value (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) 1).hom
      (singularWindingCochain X g hg) s = singularWindingValue X g hg s := by
  unfold singularWindingCochain
  rw [Iso.inv_hom_id_apply]

theorem singularWindingCochain_closed :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d 1 2 (singularWindingCochain X g hg) = 0 := by
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) 2).toLinearEquiv.injective
  ext s
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) 2).hom
    ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d 1 2 (singularWindingCochain X g hg)) s =
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) 2).hom 0 s
  rw [AlgebraicTopology.Cohomology.Singular.Formulas.degreewiseFunctionIso_coboundary, Fin.sum_univ_three]
  simp only [Fin.val_zero, pow_zero, one_zsmul,
    Fin.val_one, pow_one, neg_one_zsmul, Fin.val_two, neg_sq, one_pow, map_zero]
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) 1).hom
      (singularWindingCochain X g hg) ((TopCat.toSSet.obj X).δ 0 s) +
    -(AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) 1).hom
      (singularWindingCochain X g hg) ((TopCat.toSSet.obj X).δ 1 s) +
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) 1).hom
      (singularWindingCochain X g hg) ((TopCat.toSSet.obj X).δ 2 s) = 0
  rw [singularWindingCochain_value, singularWindingCochain_value, singularWindingCochain_value]
  simpa only [sub_eq_add_neg] using singularWindingValue_triangle X g hg s

def singularWindingCocycle : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X 1 :=
  ⟨singularWindingCochain X g hg, by
    rw [AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff]
    exact singularWindingCochain_closed X g hg⟩

def singularWindingClass : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X 1 :=
  AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) X 1 (singularWindingCocycle X g hg)

end

section

/-!
# ChernClass: naturality and local primitives of singular winding

The path-lift construction commutes with every continuous map. On a domain
carrying one logarithm, the winding cocycle is the singular coboundary of the
actual integral difference from the principal pointwise logarithm.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped Simplicial

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section

variable {X Y : TopCat.{0}} (f : Y ⟶ X) (g : C(X, ℂ)) (hg : ∀ x, g x ≠ 0)

theorem singularLogIncrement_naturality (s : (TopCat.toSSet.obj Y) _⦋1⦌) :
    singularLogIncrement X g hg ((TopCat.toSSet.map f).app _ s) =
      singularLogIncrement Y (g.comp f.hom) (fun y => hg (f y)) s := by
  exact singularLogIncrement_of_log X g hg _
    (singularSimplexLog Y (g.comp f.hom) (fun y => hg (f y)) s)
    (singularSimplexLog_exp Y (g.comp f.hom) (fun y => hg (f y)) s)

theorem singularWindingValue_naturality (s : (TopCat.toSSet.obj Y) _⦋1⦌) :
    singularWindingValue X g hg ((TopCat.toSSet.map f).app _ s) =
      singularWindingValue Y (g.comp f.hom) (fun y => hg (f y)) s := by
  apply (Rat.cast_injective (α := ℂ))
  apply mul_right_cancel₀ Complex.two_pi_I_ne_zero
  rw [singularWindingValue_period, singularWindingValue_period, singularLogIncrement_naturality]
  rfl

/-- Pullback of the actual winding cochain equals winding of the composite. -/
theorem singularWindingCochain_naturality :
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) f).f 1 (singularWindingCochain X g hg) =
      singularWindingCochain Y (g.comp f.hom) (fun y => hg (f y)) := by
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj Y) (ModuleCat.of ℚ ℚ) 1).toLinearEquiv.injective
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj Y) (ModuleCat.of ℚ ℚ) 1).hom _ =
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj Y) (ModuleCat.of ℚ ℚ) 1).hom _
  ext s
  have h := AlgebraicTopology.Cohomology.Singular.Formulas.degreewiseFunctionIso_pullback (ModuleCat.of ℚ ℚ) (TopCat.toSSet.map f)
    (singularWindingCochain X g hg) s
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj Y) (ModuleCat.of ℚ ℚ) 1).hom
      ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) f).f 1 (singularWindingCochain X g hg)) s =
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) 1).hom
      (singularWindingCochain X g hg) ((TopCat.toSSet.map f).app _ s) at h
  rw [h, singularWindingCochain_value, singularWindingCochain_value]
  exact singularWindingValue_naturality f g hg s

/-- Naturality holds in the existing rational singular cohomology. -/
theorem singularWindingClass_naturality :
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f 1 (singularWindingClass X g hg) =
      singularWindingClass Y (g.comp f.hom) (fun y => hg (f y)) := by
  unfold singularWindingClass
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.singularCohomologyPullback_class]
  congr 1
  apply Subtype.ext
  exact singularWindingCochain_naturality f g hg

/-- The endpoint of an actual singular edge is its indicated geometric vertex. -/
theorem singularEdge_vertex (s : (TopCat.toSSet.obj X) _⦋1⦌) (i : Fin 2) :
    TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj X).δ i s) =
      X.toSSetObjEquiv _ s (Convexity.StdSimplex.single (i.succAbove 0)) := by
  change X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i s) default = _
  rw [show (default : Convexity.StdSimplex ℝ (Fin 1)) = Convexity.StdSimplex.single 0 from Subsingleton.elim _ _,
    TopCat.toSSetObjEquiv_δ_apply, Convexity.StdSimplex.map_single]

end

variable (X : TopCat.{0}) (g : C(X, ℂ)) (hg : ∀ x, g x ≠ 0)
variable (l : C(X, ℂ)) (hl : ∀ x, Complex.exp (l x) = g x)

/-- An actual integer difference of logarithms at one point. -/
def pointLogPeriod (x : X) : ℚ :=
  Logarithms.Construction.logarithmicDefect (l x) 0 (Complex.log (g x))
    (by rw [Complex.exp_zero, mul_one, hl, Complex.exp_log (hg x)])

theorem pointLogPeriod_spec (x : X) :
    (pointLogPeriod X g hg l hl x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
      l x - Complex.log (g x) := by
  unfold pointLogPeriod
  push_cast
  have h := Logarithms.Construction.logarithmicDefect_spec (l x) 0 (Complex.log (g x))
    (by rw [Complex.exp_zero, mul_one, hl, Complex.exp_log (hg x)])
  simpa only [add_zero] using h.symm

/-- Principal pointwise logarithms need not be continuous; their difference
from a continuous branch is nevertheless an honest singular zero-cochain. -/
def pointLogPrimitive : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X 0 :=
  (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℚ ℚ) X).inv (pointLogPeriod X g hg l hl)

theorem pointLogPrimitive_value (x : X) :
    (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℚ ℚ) X).hom (pointLogPrimitive X g hg l hl) x =
      pointLogPeriod X g hg l hl x := by
  unfold pointLogPrimitive
  rw [Iso.inv_hom_id_apply]

/-- This is the actual local primitive, with its sign fixed by endpoint order. -/
theorem pointLogPrimitive_d :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d 0 1 (pointLogPrimitive X g hg l hl) =
      singularWindingCochain X g hg := by
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) 1).toLinearEquiv.injective
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) 1).hom _ =
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) 1).hom _
  ext s
  rw [AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCoboundary_apply, pointLogPrimitive_value, pointLogPrimitive_value,
    singularWindingCochain_value, singularEdge_vertex, singularEdge_vertex]
  apply (Rat.cast_injective (α := ℂ))
  apply mul_right_cancel₀ Complex.two_pi_I_ne_zero
  push_cast
  rw [sub_mul, pointLogPeriod_spec, pointLogPeriod_spec, singularWindingValue_period]
  have hi := singularLogIncrement_of_log X g hg s (l.comp (X.toSSetObjEquiv _ s))
    (fun x => hl (X.toSSetObjEquiv _ s x))
  rw [hi]
  change (l (X.toSSetObjEquiv _ s (Convexity.StdSimplex.single 1)) -
      Complex.log (g (X.toSSetObjEquiv _ s (Convexity.StdSimplex.single 1)))) -
    (l (X.toSSetObjEquiv _ s (Convexity.StdSimplex.single 0)) -
      Complex.log (g (X.toSSetObjEquiv _ s (Convexity.StdSimplex.single 0)))) =
    (l (X.toSSetObjEquiv _ s (Convexity.StdSimplex.single 1)) - l (X.toSSetObjEquiv _ s (Convexity.StdSimplex.single 0))) +
      Complex.log (g (X.toSSetObjEquiv _ s (Convexity.StdSimplex.single 0))) -
      Complex.log (g (X.toSSetObjEquiv _ s (Convexity.StdSimplex.single 1)))
  ring

end

/-!
# ChernClass: the actual cochain correction between two local equations

If `f = exp(l) * g`, the pointwise integer logarithmic defect of `l`,
`log(g)`, and `log(f)` is a singular zero-cochain. Its differential is the
difference of the actual winding cochains. On triple overlaps its alternating
sum is exactly the integral Chern defect of the transition logarithms.
-/

open _root_.CategoryTheory
open scoped Simplicial

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section

variable (X : TopCat.{0}) (f g : C(X, ℂ))
variable (hf : ∀ x, f x ≠ 0) (hg : ∀ x, g x ≠ 0)
variable (l : C(X, ℂ)) (hl : ∀ x, Complex.exp (l x) * g x = f x)

include hl in
/-- An actual lift of the logarithm of `g`, plus `l`, lifts the logarithm of `f`. -/
theorem singularLogIncrement_gauge (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    singularLogIncrement X f hf s = singularLogIncrement X g hg s +
      l (X.toSSetObjEquiv _ s (Convexity.StdSimplex.single 1)) -
      l (X.toSSetObjEquiv _ s (Convexity.StdSimplex.single 0)) := by
  let k := (l.comp (X.toSSetObjEquiv _ s)) + singularSimplexLog X g hg s
  have hk : ∀ x, Complex.exp (k x) = simplexFunction X f s x := by
    intro x
    change Complex.exp (l (X.toSSetObjEquiv _ s x) + singularSimplexLog X g hg s x) = _
    rw [Complex.exp_add, singularSimplexLog_exp]
    exact hl (X.toSSetObjEquiv _ s x)
  rw [singularLogIncrement_of_log X f hf s k hk]
  simp only [k, ContinuousMap.add_apply, ContinuousMap.comp_apply, singularLogIncrement]
  ring

/-- The integer discrepancy of the actual pointwise logarithms. -/
def windingGaugePeriod (x : X) : ℚ :=
  Logarithms.Construction.logarithmicDefect (l x) (Complex.log (g x)) (Complex.log (f x))
    (by rw [Complex.exp_log (hg x), Complex.exp_log (hf x)]; exact hl x)

theorem windingGaugePeriod_spec (x : X) :
    (windingGaugePeriod X f g hf hg l hl x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
      l x + Complex.log (g x) - Complex.log (f x) := by
  unfold windingGaugePeriod
  push_cast
  exact (Logarithms.Construction.logarithmicDefect_spec _ _ _ _).symm

/-- The pointwise discrepancy as a genuine singular zero-cochain. -/
def windingGaugePrimitive : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X 0 :=
  (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℚ ℚ) X).inv
    (windingGaugePeriod X f g hf hg l hl)

theorem windingGaugePrimitive_value (x : X) :
    (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℚ ℚ) X).hom
      (windingGaugePrimitive X f g hf hg l hl) x = windingGaugePeriod X f g hf hg l hl x := by
  unfold windingGaugePrimitive
  rw [Iso.inv_hom_id_apply]

/-- This primitive computes the difference before passage to cohomology. -/
theorem windingGaugePrimitive_d :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d 0 1 (windingGaugePrimitive X f g hf hg l hl) =
      singularWindingCochain X f hf - singularWindingCochain X g hg := by
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) 1).toLinearEquiv.injective
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) 1).hom _ =
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) 1).hom _
  ext s
  rw [AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCoboundary_apply, windingGaugePrimitive_value, windingGaugePrimitive_value,
    map_sub]
  dsimp only [Pi.sub_apply]
  rw [singularWindingCochain_value, singularWindingCochain_value,
    singularEdge_vertex, singularEdge_vertex]
  apply (Rat.cast_injective (α := ℂ))
  apply mul_right_cancel₀ Complex.two_pi_I_ne_zero
  push_cast
  rw [sub_mul, sub_mul, windingGaugePeriod_spec, windingGaugePeriod_spec,
    singularWindingValue_period, singularWindingValue_period,
    singularLogIncrement_gauge X f g hf hg l hl]
  simp only [simplexFunction, ContinuousMap.comp_apply]
  change (l (X.toSSetObjEquiv _ s (Convexity.StdSimplex.single 1)) +
      Complex.log (g (X.toSSetObjEquiv _ s (Convexity.StdSimplex.single 1))) -
      Complex.log (f (X.toSSetObjEquiv _ s (Convexity.StdSimplex.single 1)))) -
    (l (X.toSSetObjEquiv _ s (Convexity.StdSimplex.single 0)) +
      Complex.log (g (X.toSSetObjEquiv _ s (Convexity.StdSimplex.single 0))) -
      Complex.log (f (X.toSSetObjEquiv _ s (Convexity.StdSimplex.single 0)))) = _
  ring

end

variable (X : TopCat.{0}) (f₀ f₁ f₂ : C(X, ℂ))
variable (h₀ : ∀ x, f₀ x ≠ 0) (h₁ : ∀ x, f₁ x ≠ 0) (h₂ : ∀ x, f₂ x ≠ 0)
variable (l₀₁ l₀₂ l₁₂ : C(X, ℂ))
variable (h₀₁ : ∀ x, Complex.exp (l₀₁ x) * f₁ x = f₀ x)
variable (h₀₂ : ∀ x, Complex.exp (l₀₂ x) * f₂ x = f₀ x)
variable (h₁₂ : ∀ x, Complex.exp (l₁₂ x) * f₂ x = f₁ x)

include h₂ h₀₁ h₀₂ h₁₂ in
/-- Actual equations force the multiplicative cocycle relation between their logarithms. -/
theorem equationLog_cocycle (x : X) :
    Complex.exp (l₀₁ x) * Complex.exp (l₁₂ x) = Complex.exp (l₀₂ x) := by
  apply mul_right_cancel₀ (h₂ x)
  rw [mul_assoc, h₁₂, h₀₁, h₀₂]

/-- The triple-overlap correction is exactly the Chern logarithmic defect. -/
theorem windingGaugePeriod_triangle (x : X) :
    windingGaugePeriod X f₁ f₂ h₁ h₂ l₁₂ h₁₂ x -
      windingGaugePeriod X f₀ f₂ h₀ h₂ l₀₂ h₀₂ x +
      windingGaugePeriod X f₀ f₁ h₀ h₁ l₀₁ h₀₁ x =
    (Logarithms.Construction.logarithmicDefect (l₀₁ x) (l₁₂ x) (l₀₂ x)
      (equationLog_cocycle X f₀ f₁ f₂ h₂ l₀₁ l₀₂ l₁₂ h₀₁ h₀₂ h₁₂ x) : ℚ) := by
  apply (Rat.cast_injective (α := ℂ))
  apply mul_right_cancel₀ Complex.two_pi_I_ne_zero
  push_cast
  rw [add_mul, sub_mul, windingGaugePeriod_spec, windingGaugePeriod_spec,
    windingGaugePeriod_spec, ← Logarithms.Construction.logarithmicDefect_spec]
  ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.WindingSingular
