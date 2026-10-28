import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BirationalDivisor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.ImageDimension

/-! # Birational Principal Divisor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BirationalPrincipalDivisor

noncomputable section

/-! Full principal-divisor pushforward for a proper birational morphism
to a scheme regular at its divisor points. Exceptional divisor terms have
zero native residue degree, as proved from their dimension. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm

theorem pointPushforward_eq_zero_of_degrees {X Y : Scheme} (f : X ⟶ Y)
    (c : X →₀ ℚ) (y : Y)
    (h : ∀ x : X, c x ≠ 0 → f x = y → f.residueDegree x = 0) :
    CyclePushforward.pointPushforward f c y = 0 := by
  classical
  rw [CyclePushforward.pointPushforward, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro x hx
  by_cases hxy : f x = y
  · rw [h x (Finsupp.mem_support_iff.mp hx) hxy, Nat.cast_zero, Finsupp.single_zero,
      smul_zero, Finsupp.zero_apply]
  · rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne (fun he => hxy he.symm), smul_zero]

theorem dimension_eq_of_birational {K : Type} [Field K]
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y)
    [IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη)] (g : Y ⟶ Spec (.of K)) :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ g) := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra g
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (f ≫ g)
  let e := AlgEquiv.ofBijective (Cycles.Functoriality.FunctionFields.Construction.genericFieldAlgHom f hη g)
    ((ConcreteCategory.isIso_iff_bijective (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη)).mp inferInstance)
  exact congrArg Cardinal.toNat e.trdeg_eq

/-- Proper birational pushforward preserves the full finite principal
divisor, including the vanishing of every exceptional contribution. -/
theorem principalDivisor_pushforward {K : Type} [Field K]
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (hη : f (genericPoint X) = genericPoint Y)
    [IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη)] (gY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType gY]
    (hDVR : ∀ y : Y, coheight y = 1 → IsDiscreteValuationRing (Y.presheaf.stalk y))
    (g : Y.functionField) :
    CyclePushforward.pointPushforward f (Affine.DivisorNorm.rationalPrincipalDivisor X (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη g)) =
      Affine.DivisorNorm.rationalPrincipalDivisor Y g := by
  ext y
  by_cases hy : coheight y = 1
  · let := hDVR y hy
    exact BirationalDivisor.principalDivisor_coefficient f hη y g
  · rw [Affine.DivisorNorm.rationalPrincipalDivisor_apply, Scheme.ord_eq_zero_of_coheight_neq_one hy, Int.cast_zero]
    apply pointPushforward_eq_zero_of_degrees
    intro x hx hxy
    by_contra hd
    have hxone : coheight x = 1 := by
      by_contra hn
      apply hx
      rw [Affine.DivisorNorm.rationalPrincipalDivisor_apply, Scheme.ord_eq_zero_of_coheight_neq_one hn, Int.cast_zero]
    have himage := Divisor.ImageDimension.coheight_image_eq_one f gY
      (dimension_eq_of_birational f hη gY) x hxone hd
    exact hy (hxy ▸ himage)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BirationalPrincipalDivisor
