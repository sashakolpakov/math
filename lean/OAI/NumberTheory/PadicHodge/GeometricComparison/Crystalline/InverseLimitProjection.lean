import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.InverseLimitCoordinates

/-! # Inverse Limit Projection -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.InverseLimitProjection.CrystallineInverseLimitProjection

noncomputable section

/-! The categorical projections of the original crystalline inverse
limit equivalence are the original bounded crystalline restriction maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionComplexExact.sequence (p := p) (J := J) (δ := δ) f

theorem eval (i : ℕ) [Mono (HomologicalComplex.homologyMap (S).f i)]
    (x : IntegralComparison.BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f i) (n : ℕ) :
    limit.π (IntegralComparison.Crystalline.FiniteInverseLimit.diagram f i) (op n)
      (IntegralComparison.Crystalline.FiniteInverseLimit.linearEquiv f i x) =
        IntegralComparison.BoundedCrystalline.CrystallineCohomology.restriction f n i x := by
  rw [IntegralComparison.Crystalline.FiniteInverseLimit.linearEquiv_apply]
  have h := (IntegralComparison.SequentialKernelLimit.isLimit R
    (fun k => IntegralComparison.BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f k i)
    (fun k => IntegralComparison.Crystalline.CohomologyDifference.transition (p := p) (J := J) (δ := δ) f k i)).conePointUniqueUpToIso_hom_comp
      (limit.isLimit (IntegralComparison.Crystalline.FiniteInverseLimit.diagram f i)) (op n)
  exact (ConcreteCategory.congr_hom h (IntegralComparison.Crystalline.FiniteInverseLimit.compatibleLinearEquiv f i x)).trans
    (IntegralComparison.Crystalline.InverseLimitCoordinates.compatible_coordinate f i x n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.InverseLimitProjection.CrystallineInverseLimitProjection
