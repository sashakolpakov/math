import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineInverseLimit
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineTowerCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.InverseLimitProjection

/-! # Crystalline Inverse Limit Projection -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineInverseLimitProjection.IntrinsicPadicCrystallineInverseLimitProjection

noncomputable section

/-! The original smooth proper crystalline inverse-limit isomorphism
has the original bounded crystalline restrictions as its projections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsProper Y.hom] [Smooth Y.hom]
  (hprojective : IntegralComparison.Projectivity.Construction.ProjectiveOver (ZMod p) Y.hom)

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y

theorem eval (x : IntegralComparison.BigCrystallineCohomology.Cohomology (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w 1) (n : ℕ) :
    limit.π (CrystallineTowerCoordinates.IntrinsicPadicCrystallineTowerCoordinates.original p Y) (op n)
      ((CrystallineInverseLimit.IntrinsicPadicCrystallineInverseLimit.iso p Y hprojective).hom x) =
        IntegralComparison.BoundedCrystalline.CrystallineCohomology.restriction w n 1 x := by
  let := IntegralComparison.SmoothProper.CrystallineInverseLimit.inclusion_mono p (ZMod p) Y hprojective 1
  exact Crystalline.InverseLimitProjection.CrystallineInverseLimitProjection.eval w 1 x n

theorem hom_π (n : ℕ) : (CrystallineInverseLimit.IntrinsicPadicCrystallineInverseLimit.iso p Y hprojective).hom ≫
    limit.π (CrystallineTowerCoordinates.IntrinsicPadicCrystallineTowerCoordinates.original p Y) (op n) =
      ModuleCat.ofHom (IntegralComparison.BoundedCrystalline.CrystallineCohomology.restriction w n 1) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact eval p Y hprojective x n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineInverseLimitProjection.IntrinsicPadicCrystallineInverseLimitProjection
