import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PeriodSurjectivityOne
import OAI.AlgebraicGeometry.DivisorClass.Chern.Logarithms
import Mathlib.Analysis.Complex.CoveringMap

/-! # Exponential Cocycle Q -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialCocycleQ.Constructions.ExponentialCocycle

noncomputable section

/-!
# DegreeTwo: genuine singular cocycles from the exponential covering

An additive rational functional on the complex logarithm plane gives endpoint
differences of lifted edges. Continuous logarithm lifts differ by one constant
integral period on a connected simplex, so these differences descend to an
actual singular cocycle on the punctured complex plane.
-/

open _root_.CategoryTheory Opposite
open scoped Simplicial
open OAI.AlgebraicGeometry.DivisorClass.Chern.Logarithms.Construction

abbrev Plane := TopCat.of ℂ
abbrev Punctured := TopCat.of {z : ℂ // z ≠ 0}
abbrev Q := ModuleCat.of ℚ ℚ

/-- The actual exponential covering, with its nonzero codomain. -/
def exponentialMap : Plane ⟶ Punctured :=
  TopCat.ofHom ⟨fun z => ⟨Complex.exp z, Complex.exp_ne_zero z⟩,
    Complex.continuous_exp.subtype_mk _⟩

theorem exponentialMap_covering : IsCoveringMap exponentialMap := Complex.isCoveringMap_exp

theorem exponentialMap_surjective : Function.Surjective exponentialMap := by
  intro z
  exact ⟨Complex.log z.val, Subtype.ext (Complex.exp_log z.property)⟩

/-- Two actual logarithm lifts on a connected space differ by a constant. -/
theorem logarithm_difference_constant {S : Type} [TopologicalSpace S] [PreconnectedSpace S]
    (a b : C(S, ℂ)) (hab : ∀ s, Complex.exp (a s) = Complex.exp (b s)) (s t : S) :
    a s - b s = a t - b t := by
  have h (x : S) : Complex.exp (a x) * Complex.exp (0 : ℂ) = Complex.exp (b x) := by
    simpa only [Complex.exp_zero, mul_one] using hab x
  have hl := DivisorClass.Chern.Logarithms.Construction.isLocallyConstant_logarithmicDefect a 0 b h
  have he := congrArg (fun n : ℤ => (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
    (hl.apply_eq_of_preconnectedSpace s t)
  simp only [ContinuousMap.zero_apply] at he
  rw [← DivisorClass.Chern.Logarithms.Construction.logarithmicDefect_spec (a s) 0 (b s) (h s),
    ← DivisorClass.Chern.Logarithms.Construction.logarithmicDefect_spec (a t) 0 (b t) (h t)] at he
  simpa only [add_zero] using he

variable (F : ℂ →+ ℚ)

abbrev primitiveZeroCochain : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains Q Plane).X 0 :=
  PeriodSurjectivityOne.Constructions.PeriodSurjectivity.additiveZeroCochain F

/-- Endpoint differences of the additive functional agree for every lift of an edge. -/
theorem primitiveCoboundary_lift_independent (s t : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices Plane 1)
    (hst : (TopCat.toSSet.map exponentialMap).app (op ⦋1⦌) s =
      (TopCat.toSSet.map exponentialMap).app (op ⦋1⦌) t) :
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj Plane) Q 1).hom
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains Q Plane).d 0 1 (primitiveZeroCochain F)) s =
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj Plane) Q 1).hom
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains Q Plane).d 0 1 (primitiveZeroCochain F)) t := by
  let a := TopCat.toSSetObj₁Equiv s
  let b := TopCat.toSSetObj₁Equiv t
  let : PreconnectedSpace TopCat.I := by
    constructor
    rw [← TopCat.I.homeomorph.symm.surjective.range_eq]
    exact isPreconnected_range TopCat.I.homeomorph.symm.continuous
  have hab (x : TopCat.I) : Complex.exp (a x) = Complex.exp (b x) :=
    congrArg (fun u : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices Punctured 1 => (TopCat.toSSetObj₁Equiv u x).val) hst
  have hd := congrArg F (logarithm_difference_constant a.hom b.hom hab 1 0)
  rw [map_sub, map_sub] at hd
  rw [PeriodSurjectivityOne.Constructions.PeriodSurjectivity.additiveCoboundary_apply, PeriodSurjectivityOne.Constructions.PeriodSurjectivity.additiveCoboundary_apply]
  exact sub_eq_sub_iff_sub_eq_sub.mp hd

/-- A chosen continuous logarithm lift of a genuine singular edge. -/
def edgeLift (s : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices Punctured 1) : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices Plane 1 :=
  (SingularCoveringLift.Constructions.SingularCovering.singularSimplex_map_surjective exponentialMap exponentialMap_covering
    exponentialMap_surjective 1 s).choose

theorem edgeLift_spec (s : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices Punctured 1) :
    (TopCat.toSSet.map exponentialMap).app (op ⦋1⦌) (edgeLift s) = s :=
  (SingularCoveringLift.Constructions.SingularCovering.singularSimplex_map_surjective exponentialMap exponentialMap_covering
    exponentialMap_surjective 1 s).choose_spec

/-- The actual rational singular one-cochain given by lifted endpoint differences. -/
def oneCochain : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains Q Punctured).X 1 :=
  (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj Punctured) Q 1).inv
    (fun s => (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj Plane) Q 1).hom
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains Q Plane).d 0 1 (primitiveZeroCochain F)) (edgeLift s))

theorem oneCochain_apply (s : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices Punctured 1) :
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj Punctured) Q 1).hom (oneCochain F) s =
      (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj Plane) Q 1).hom
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains Q Plane).d 0 1 (primitiveZeroCochain F)) (edgeLift s) := by
  unfold oneCochain
  rw [Iso.inv_hom_id_apply]

/-- Pullback to the actual logarithm plane is exactly the original coboundary. -/
theorem oneCochain_pullback :
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback Q exponentialMap).f 1 (oneCochain F) =
      (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains Q Plane).d 0 1 (primitiveZeroCochain F) := by
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj Plane) Q 1).toLinearEquiv.injective
  ext s
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj Plane) Q 1).hom
    ((AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback Q (TopCat.toSSet.map exponentialMap)).f 1 (oneCochain F)) s = _
  rw [AlgebraicTopology.Cohomology.Singular.Formulas.degreewiseFunctionIso_pullback, oneCochain_apply]
  exact primitiveCoboundary_lift_independent F _ s (edgeLift_spec _)

/-- Closedness is verified after injective actual cochain pullback to the covering. -/
theorem oneCochain_closed : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains Q Punctured).d 1 2 (oneCochain F) = 0 := by
  apply SingularCoveringLift.Constructions.SingularCovering.singularPullback_injective exponentialMap exponentialMap_covering
    exponentialMap_surjective Q 2
  rw [map_zero]
  have hc := ConcreteCategory.congr_hom ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback Q exponentialMap).comm 1 2)
    (oneCochain F)
  change (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains Q Plane).d 1 2
      ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback Q exponentialMap).f 1 (oneCochain F)) =
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback Q exponentialMap).f 2 ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains Q Punctured).d 1 2 (oneCochain F)) at hc
  rw [← hc, oneCochain_pullback]
  exact ConcreteCategory.congr_hom ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains Q Plane).d_comp_d 0 1 2)
    (primitiveZeroCochain F)

def cocycle : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains Q Punctured) 1 :=
  ⟨oneCochain F, (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff _ _ _).mpr (oneCochain_closed F)⟩

/-- Every actual local logarithm pulls the cocycle back to its zero-cochain primitive. -/
theorem localPrimitive {Y : TopCat.{0}} (g : Y ⟶ Punctured) (b : Y ⟶ Plane)
    (hb : b ≫ exponentialMap = g) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains Q Y).d 0 1 ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback Q b).f 0 (primitiveZeroCochain F)) =
      (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback Q g).f 1 (oneCochain F) := by
  rw [SingularPeriodsD.Constructions.SingularPeriods.zeroPullback_d, ← oneCochain_pullback F]
  change ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback Q exponentialMap ≫ AlgebraicTopology.Cohomology.Singular.Functor.singularPullback Q b).f 1) (oneCochain F) = _
  rw [← AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp, hb]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialCocycleQ.Constructions.ExponentialCocycle
