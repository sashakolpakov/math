import OAI.AlgebraicGeometry.Divisors.LineBundles.BirationalValuationPrincipal
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GenericDimension
import OAI.AlgebraicGeometry.Divisors.LineBundles.CodimensionOneDimensionConverse

/-! # Birational Principal Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.BirationalPrincipalDivisor.BundleCycles

noncomputable section

/-! # LineBundleCycles: proper birational pushforward preserves the complete actual principal divisor over a target regular in codimension one -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

theorem pointPushforward_eq_zero_of_degrees {X Y : Scheme} (f : X ⟶ Y)
    (c : X →₀ ℚ) (y : Y)
    (h : ∀ x, c x ≠ 0 → f x = y → f.residueDegree x = 0) : IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f c y = 0 := by
  classical
  rw [IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro x hx
  by_cases hxy : f x = y
  · rw [h x (Finsupp.mem_support_iff.mp hx) hxy, Nat.cast_zero, Finsupp.single_zero, smul_zero, Finsupp.zero_apply]
  · rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne (fun he => hxy he.symm), smul_zero]

theorem schemeDimension_eq_of_birational {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y)
    [IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη)] (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ g) := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra g
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (f ≫ g)
  let e := AlgEquiv.ofBijective (Cycles.Functoriality.FunctionFields.Construction.genericFieldAlgHom f hη g)
    ((ConcreteCategory.isIso_iff_bijective (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη)).mp inferInstance)
  exact congrArg Cardinal.toNat e.trdeg_eq

theorem properBirational_principalDivisor_pushforward {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (hη : f (genericPoint X) = genericPoint Y)
    [IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη)] (gY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType gY]
    (hDVR : ∀ y : Y, coheight y = 1 → IsDiscreteValuationRing (Y.presheaf.stalk y)) (g : Y.functionField) :
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη g)) =
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Y g := by
  ext y
  by_cases hy : coheight y = 1
  · let := hDVR y hy
    exact BirationalValuationPrincipal.BundleCycles.BirationalValuationDivisor.principalDivisor_coefficient f hη y g
  · rw [RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, Scheme.ord_eq_zero_of_coheight_neq_one hy, Int.cast_zero]
    apply pointPushforward_eq_zero_of_degrees
    intro x hx hxy
    by_contra hd
    have hxone : coheight x = 1 := by
      by_contra hn
      apply hx
      rw [RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, Scheme.ord_eq_zero_of_coheight_neq_one hn, Int.cast_zero]
    have himage : coheight (f x) = 1 := by
      apply CodimensionOneDimensionConverse.BundleCycles.pointCoheight_one_of_dimension_drop gY (f x)
      rw [Finite.GenericDimension.BundleCycles.pointClosure_dimension_of_nonzeroResidueDegree f gY x hd,
        schemeDimension_eq_of_birational f hη gY]
      exact DivisorClass.Chern.SupportCodimension.Construction.pointClosure_dimension_add_one (f ≫ gY) x hxone
    exact hy (hxy ▸ himage)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.BirationalPrincipalDivisor.BundleCycles
