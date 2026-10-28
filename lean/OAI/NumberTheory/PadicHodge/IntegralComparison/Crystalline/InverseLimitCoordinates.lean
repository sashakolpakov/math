import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.FiniteInverseLimit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RestrictionJointKernel

/-! # Inverse Limit Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.InverseLimitCoordinates

noncomputable section

/-! Coordinates of the original crystalline inverse-limit equivalence are the actual bounded restriction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionComplexExact.sequence (p := p) (J := J) (δ := δ) f

theorem source_coordinate (i : ℕ) (x : (S).X₁.homology i) :
    (BoundedCohomologySequence.sourceIso f i).hom (ULift.up x) =
      RestrictionJointKernel.sourceEquiv f i x := by
  let e := BoundedResolution.Comparison.homologyIso (p := p) (J := J) (δ := δ) f i
  let c := ((S).X₁.sc i).mapHomologyIso (ModuleCat.uliftFunctor.{u + 2, u + 1} R)
  let K : CochainComplex (ModuleCat.{u + 2} R) ℕ :=
    BoundedResolution.Comparison.complex (p := p) (J := J) (δ := δ) f
  change e.hom (HomologicalComplex.homologyMap (𝟙 K) i (c.inv (ULift.up x))) =
    e.hom (c.inv (ULift.up x))
  rw [HomologicalComplex.homologyMap_id]
  rfl

theorem middle_coordinate (i n : ℕ)
    (x : BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f i) :
    (BoundedCohomologySequence.middle f i).f x n =
      BoundedCrystalline.CrystallineCohomology.restriction f n i x := by
  let e := RestrictionJointKernel.sourceEquiv (p := p) (J := J) (δ := δ) f i
  let y := e.symm x
  have hy : e y = x := e.apply_symm_apply x
  have hc : (BoundedCohomologySequence.sourceIso f i).inv x = ULift.up y := by
    apply (BoundedCohomologySequence.sourceIso f i).toLinearEquiv.injective
    exact ((BoundedCohomologySequence.sourceIso f i).toLinearEquiv.apply_symm_apply x).trans
      ((source_coordinate f i y).trans hy).symm
  change BoundedProductCohomology.productHomologyLinearEquiv f i
    (HomologicalComplex.homologyMap (S).f i
      ((BoundedCohomologySequence.sourceIso f i).inv x).down) n = _
  rw [hc]
  exact (RestrictionJointKernel.product_coordinate f n i y).trans
    (congrArg (BoundedCrystalline.CrystallineCohomology.restriction f n i) hy)

theorem compatible_coordinate (i : ℕ) [Mono (HomologicalComplex.homologyMap (S).f i)]
    (x : BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f i) (n : ℕ) :
    (FiniteInverseLimit.compatibleLinearEquiv f i x).val n =
      BoundedCrystalline.CrystallineCohomology.restriction f n i x :=
  middle_coordinate f i n x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.InverseLimitCoordinates
