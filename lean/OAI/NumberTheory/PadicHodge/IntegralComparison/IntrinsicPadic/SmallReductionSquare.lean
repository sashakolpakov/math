import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SmallCohomology
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineRestrictionExt

/-! # Small Reduction Square -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SmallReductionSquare.Intrinsic

noncomputable section

/-! The accepted integral H¹ comparison reduces to the full ordinary
finite-level Čech comparison, with the original three-term coordinate
isomorphism made explicit. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

private theorem descent_comp
    {R S : Type*} [CommRing R] [CommRing S]
    (F : ModuleCat.{0} R ⥤ ModuleCat.{2} S)
    (G : ModuleCat.{2} S ⥤ ModuleCat.{2} R)
    (η : ∀ M : ModuleCat.{0} R, M ≃ₗ[R] G.obj (F.obj M))
    (hη : ∀ {M N : ModuleCat.{0} R} (a : M ⟶ N) (x : M), η N (a x) = G.map (F.map a) (η M x))
    {M N : ModuleCat.{0} R} {P : ModuleCat.{2} S}
    (e : M ≅ N) (u : F.obj N ≅ P) (x : M) :
    ((η M).trans ((G.mapIso (F.mapIso e ≪≫ u)).toLinearEquiv)) x =
      ((η N).trans ((G.mapIso u).toLinearEquiv)) (e.hom x) := by
  change G.map (F.map e.hom ≫ u.hom) (η M x) = G.map u.hom (η N (e.hom x))
  rw [Functor.map_comp, hη]
  rfl

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsProper Y.hom] [Smooth Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (I : InjectiveResolution (BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (Witt.Crystalline.wittStructureMap p (ZMod p) Y)))
  (hprojective : Projectivity.Construction.ProjectiveOver (ZMod p) Y.hom)

local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.complex ℤ_[p] X
  (GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X)

omit hprojective [Smooth Y.hom] in
theorem finiteEquiv_eq (n : ℕ)
    (x : GeometricComparison.CochainQuotientCohomology.PrincipalCochainQuotient.cohomology ℤ_[p] K (p : ℤ_[p]) (n+1) 1) :
    GeometricComparison.IntrinsicPadic.CrystallineRestrictionExt.IntrinsicPadicIntegralCrystallineReduction.finiteEquiv p X Y f hp I n x =
      SmallCohomology.Intrinsic.linearEquiv p X Y f hp I n 1
        ((GeometricComparison.IntrinsicPadic.FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X n).inv x) :=
  descent_comp (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p) (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicCoefficientDescent.restrict p)
    (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicCoefficientDescent.equiv p) (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicCoefficientDescent.natural p)
    (GeometricComparison.IntrinsicPadic.FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X n).symm
    (SmallCohomology.Intrinsic.iso p X Y f hp I n 1) x

theorem square (n : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1) :
    GeometricComparison.IntrinsicPadic.CrystallineRestrictionExt.IntrinsicPadicIntegralCrystallineReduction.restriction p Y n
        (GeometricComparison.IntrinsicPadic.IntegralCrystallineEquiv.IntrinsicPadicIntegralCrystallineEquiv.equiv p X Y f hp I hprojective x) =
      SmallCohomology.Intrinsic.linearEquiv p X Y f hp I n 1
        ((GeometricComparison.IntrinsicPadic.FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X n).inv
          (GeometricComparison.IntrinsicPadic.IntegralReductionCoordinates.IntrinsicPadicIntegralReductionCoordinates.reduction p X (n+1) x)) :=
  (LinearMap.congr_fun
    (GeometricComparison.IntrinsicPadic.CrystallineRestrictionExt.IntrinsicPadicIntegralCrystallineReduction.square p X Y f hp I hprojective n) x).trans
      (finiteEquiv_eq p X Y f hp I n _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SmallReductionSquare.Intrinsic
