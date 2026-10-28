import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.SingularPeriods
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularPeriodEquiv
import OAI.AlgebraicTopology.Cohomology.Singular.Coefficients

/-! # Singular Period Coefficients -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularPeriodCoefficients.DivisibleSingularPeriods

/-! Realize lattice characters with divisible abelian coefficients by
actual singular cocycles, with their normalized primitives. -/

open _root_.CategoryTheory Opposite
open scoped Simplicial _root_.Topology

open OAI.AlgebraicTopology.Cohomology.Singular.Coefficients
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OnePrimitives.Constructions.DegreeOnePrimitives
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularPeriodEquiv.SingularPeriodComparison (lift_difference_constant projection_covering edgeLift edgeLift_spec)

variable {R : Type} [Ring R] (M : ModuleCat.{0} R)
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (Λ : Submodule ℤ V) [DiscreteTopology Λ]

omit [NormedSpace ℝ V] [DiscreteTopology Λ] in
/-- Any divisible-group-valued character on the lattice has an additive extension to V. -/
theorem exists_additive_extension [DivisibleBy M ℤ] (φ : Λ →+ M) :
    ∃ F : V →+ M, ∀ ℓ : Λ, F ℓ = φ ℓ := by
  let : Module.Injective ℤ M := (Module.Baer.of_divisible M).injective
  obtain ⟨F, hF⟩ := Module.Injective.out Λ.subtype Λ.subtype_injective φ.toIntLinearMap
  exact ⟨F.toAddMonoidHom, hF⟩

/-- An additive function is used as a genuine singular zero-cochain. -/
def additiveZeroCochain (F : V →+ M) : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).X 0 :=
  (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).inv (fun v => F v)

omit [NormedSpace ℝ V] in
@[simp]
theorem additiveZeroCochain_value (F : V →+ M) (v : V) :
    (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).hom (additiveZeroCochain M F) v = F v := by
  change (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).hom
      ((AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).inv (fun v => F v)) v = F v
  rw [Iso.inv_hom_id_apply]

omit [NormedSpace ℝ V] in
/-- The coboundary of an additive point function is its endpoint difference. -/
theorem additiveCoboundary_apply (F : V →+ M)
    (s : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V)) 1) :
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))) M 1).hom
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 0 1 (additiveZeroCochain M F)) s =
      F (TopCat.toSSetObj₁Equiv s 1) - F (TopCat.toSSetObj₁Equiv s 0) := by
  rw [AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCoboundary_apply, additiveZeroCochain_value M, additiveZeroCochain_value M,
    TopCat.toSSetObj₁Equiv_apply_one, TopCat.toSSetObj₁Equiv_apply_zero]

omit [NormedSpace ℝ V] in
/-- Endpoint differences of an additive function are independent of the
chosen lift of a singular edge. -/
theorem additiveCoboundary_lift_invariant (F : V →+ M)
    (s t : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V)) 1)
    (hst : (TopCat.toSSet.map (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).app (op ⦋1⦌) s =
      (TopCat.toSSet.map (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).app (op ⦋1⦌) t) :
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))) M 1).hom
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 0 1 (additiveZeroCochain M F)) s =
      (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))) M 1).hom
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 0 1 (additiveZeroCochain M F)) t := by
  let a := TopCat.toSSetObj₁Equiv s
  let b := TopCat.toSSetObj₁Equiv t
  let : PreconnectedSpace TopCat.I := by
    constructor
    rw [← TopCat.I.homeomorph.symm.surjective.range_eq]
    exact isPreconnected_range TopCat.I.homeomorph.symm.continuous
  have hab (z : TopCat.I) :
      (QuotientAddGroup.mk (a z) : V ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk (b z) := by
    exact congrArg (fun u => TopCat.toSSetObj₁Equiv u z) hst
  have hd := SingularPeriodEquiv.SingularPeriodComparison.lift_difference_constant Λ a.hom b.hom hab 1 0
  have h := congrArg F hd
  rw [map_sub, map_sub] at h
  rw [additiveCoboundary_apply M, additiveCoboundary_apply M]
  change F (a 1) - F (a 0) = F (b 1) - F (b 0)
  exact sub_eq_sub_iff_sub_eq_sub.mp h

/-- Descend the coboundary of the additive extension by lifting edges. -/
def descendedOneCochain (F : V →+ M) : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)).X 1 :=
  (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)) M 1).inv
    (fun s => (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))) M 1).hom
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 0 1 (additiveZeroCochain M F)) (SingularPeriodEquiv.SingularPeriodComparison.edgeLift Λ s))

omit [NormedSpace ℝ V] in
theorem descendedOneCochain_apply (F : V →+ M) (s : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1) :
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)) M 1).hom
        (descendedOneCochain M Λ F) s =
      (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))) M 1).hom
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 0 1 (additiveZeroCochain M F)) (SingularPeriodEquiv.SingularPeriodComparison.edgeLift Λ s) := by
  unfold descendedOneCochain
  rw [Iso.inv_hom_id_apply]

omit [NormedSpace ℝ V] in
/-- Pulling back the descended cochain recovers the actual coboundary of F. -/
theorem descendedOneCochain_pullback (F : V →+ M) :
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).f 1 (descendedOneCochain M Λ F) =
      (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 0 1 (additiveZeroCochain M F) := by
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))) M 1).toLinearEquiv.injective
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))) M 1).hom
      ((AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback M (TopCat.toSSet.map (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ))).f 1 (descendedOneCochain M Λ F)) = _
  ext s
  rw [AlgebraicTopology.Cohomology.Singular.Formulas.degreewiseFunctionIso_pullback, descendedOneCochain_apply M]
  exact additiveCoboundary_lift_invariant M Λ F _ s (SingularPeriodEquiv.SingularPeriodComparison.edgeLift_spec Λ _)

omit [NormedSpace ℝ V] in
/-- The descended cochain is closed, as can be tested after pulling back
to the covering, where it is literally a coboundary. -/
theorem descendedOneCochain_closed (F : V →+ M) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)).d 1 2 (descendedOneCochain M Λ F) = 0 := by
  apply HodgeConjecture.DegreeTwo.SingularCoveringLift.Constructions.SingularCovering.singularPullback_injective (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ) (SingularPeriodEquiv.SingularPeriodComparison.projection_covering Λ)
    QuotientAddGroup.mk_surjective M 2
  rw [map_zero]
  have hcomm := ConcreteCategory.congr_hom ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).comm 1 2)
    (descendedOneCochain M Λ F)
  have hd := ConcreteCategory.congr_hom
    ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d_comp_d 0 1 2) (additiveZeroCochain M F)
  change (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 1 2
      ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).f 1 (descendedOneCochain M Λ F)) =
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).f 2
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)).d 1 2 (descendedOneCochain M Λ F)) at hcomm
  rw [← hcomm, descendedOneCochain_pullback M]
  exact hd

/-- The actual singular cocycle obtained from an additive extension. -/
def descendedCocycle (F : V →+ M) : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 :=
  ⟨descendedOneCochain M Λ F,
    (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff _ _ _).mpr (descendedOneCochain_closed M Λ F)⟩

/-- The normalized primitive of this cocycle is the original additive
function, interpreted as an actual singular zero-cochain. -/
theorem primitive_descendedCocycle (F : V →+ M) :
    Integral.SingularPeriods.IntegralSingularPeriods.primitive M Λ (descendedCocycle M Λ F) = additiveZeroCochain M F := by
  apply HodgeConjecture.DegreeTwo.OnePrimitives.Constructions.DegreeOnePrimitives.zeroCochain_eq_of_d_eq M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V)) 0
  · rw [Integral.SingularPeriods.IntegralSingularPeriods.primitive_d M]
    exact descendedOneCochain_pullback M Λ F
  · change Integral.SingularPeriods.IntegralSingularPeriods.primitiveValue M Λ (descendedCocycle M Λ F) 0 =
      (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).hom (additiveZeroCochain M F) 0
    rw [Integral.SingularPeriods.IntegralSingularPeriods.primitiveValue_zero M, additiveZeroCochain_value M, map_zero]

/-- The constructed cocycle realizes precisely the prescribed periods. -/
theorem periodHom_descendedCocycle (F : V →+ M) (ℓ : Λ) :
    Integral.SingularPeriods.IntegralSingularPeriods.periodHom M Λ (descendedCocycle M Λ F) ℓ = F ℓ := by
  change (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).hom
    (Integral.SingularPeriods.IntegralSingularPeriods.primitive M Λ (descendedCocycle M Λ F)) ℓ = F ℓ
  rw [primitive_descendedCocycle M, additiveZeroCochain_value M]

variable [DivisibleBy M ℤ]

/-- Every additive divisible-group-valued lattice character occurs as the period map
of a genuine singular H¹ class. -/
theorem cohomologyPeriod_surjective : Function.Surjective (Integral.SingularPeriods.IntegralSingularPeriods.cohomologyPeriod M Λ) := by
  intro φ
  obtain ⟨F, hF⟩ := exists_additive_extension M Λ φ
  refine ⟨AlgebraicTopology.Cohomology.Singular.Representatives.singularClass M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 (descendedCocycle M Λ F), ?_⟩
  rw [Integral.SingularPeriods.IntegralSingularPeriods.cohomologyPeriod_class M]
  ext ℓ
  exact (periodHom_descendedCocycle M Λ F ℓ).trans (hF ℓ)

/-- The actual singular H¹ of a lattice quotient is canonically its
space of additive divisible-group-valued lattice characters. -/
def cohomologyPeriodEquiv : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 ≃ₗ[R] (Λ →+ M) :=
  LinearEquiv.ofBijective (Integral.SingularPeriods.IntegralSingularPeriods.cohomologyPeriod M Λ)
    ⟨Integral.SingularPeriods.IntegralSingularPeriods.cohomologyPeriod_injective M Λ, cohomologyPeriod_surjective M Λ⟩

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularPeriodCoefficients.DivisibleSingularPeriods

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularPeriodCoefficients.IntegralSingularPeriods

/-! The constructed singular periods commute with actual coefficient maps. -/

open _root_.CategoryTheory

open OAI.AlgebraicTopology.Cohomology.Singular.Coefficients
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OnePrimitives.Constructions.DegreeOnePrimitives

variable {R : Type} [Ring R] {M N : ModuleCat.{0} R} (f : M ⟶ N)

theorem coefficient_zero_point (X : TopCat.{0})
    (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).X 0) (x : X) :
    (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso N X).hom ((AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap f X).f 0 b) x =
      f ((AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso M X).hom b x) :=
  AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap_apply f X b (TopCat.toSSetObj₀Equiv.symm x)

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (Λ : Submodule ℤ V)

theorem primitive_coefficient (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1) :
    Integral.SingularPeriods.IntegralSingularPeriods.primitive N Λ (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientCocycleMap f (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 c) =
      (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap f (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).f 0 (Integral.SingularPeriods.IntegralSingularPeriods.primitive M Λ c) := by
  apply HodgeConjecture.DegreeTwo.OnePrimitives.Constructions.DegreeOnePrimitives.zeroCochain_eq_of_d_eq N (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V)) 0
  · rw [Integral.SingularPeriods.IntegralSingularPeriods.primitive_d]
    have hd := ConcreteCategory.congr_hom
      ((AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap f (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).comm 0 1).symm (Integral.SingularPeriods.IntegralSingularPeriods.primitive M Λ c)
    have hn := ConcreteCategory.congr_hom
      (congrArg (fun g => g.f 1) (AlgebraicTopology.Cohomology.Singular.Functor.coefficientCochainMap_naturality f (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ))) c.val
    change (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap f (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).f 1
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 0 1 (Integral.SingularPeriods.IntegralSingularPeriods.primitive M Λ c)) =
      (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).d 0 1
        ((AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap f (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).f 0 (Integral.SingularPeriods.IntegralSingularPeriods.primitive M Λ c)) at hd
    rw [Integral.SingularPeriods.IntegralSingularPeriods.primitive_d] at hd
    exact hn.symm.trans hd
  · rw [coefficient_zero_point]
    change Integral.SingularPeriods.IntegralSingularPeriods.primitiveValue N Λ (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientCocycleMap f (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 c) 0 =
      f (Integral.SingularPeriods.IntegralSingularPeriods.primitiveValue M Λ c 0)
    rw [Integral.SingularPeriods.IntegralSingularPeriods.primitiveValue_zero, Integral.SingularPeriods.IntegralSingularPeriods.primitiveValue_zero, map_zero]

theorem periodHom_coefficient (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1) :
    Integral.SingularPeriods.IntegralSingularPeriods.periodHom N Λ (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientCocycleMap f (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 c) =
      f.hom.toAddMonoidHom.comp (Integral.SingularPeriods.IntegralSingularPeriods.periodHom M Λ c) := by
  ext l
  change (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso N (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V))).hom
      (Integral.SingularPeriods.IntegralSingularPeriods.primitive N Λ (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientCocycleMap f (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 c)) l = _
  rw [primitive_coefficient, coefficient_zero_point]
  rfl

theorem cohomologyPeriod_coefficient [DiscreteTopology Λ]
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1) :
    Integral.SingularPeriods.IntegralSingularPeriods.cohomologyPeriod N Λ (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap f (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 a) =
      f.hom.toAddMonoidHom.comp (Integral.SingularPeriods.IntegralSingularPeriods.cohomologyPeriod M Λ a) := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective M (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 a
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientMap_class, Integral.SingularPeriods.IntegralSingularPeriods.cohomologyPeriod_class, Integral.SingularPeriods.IntegralSingularPeriods.cohomologyPeriod_class]
  exact periodHom_coefficient f Λ c

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularPeriodCoefficients.IntegralSingularPeriods

end

end OAI
