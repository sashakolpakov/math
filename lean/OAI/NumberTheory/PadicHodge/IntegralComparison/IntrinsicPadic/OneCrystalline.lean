import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.PadicOne

/-! # One Crystalline -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.OneCrystalline.IntrinsicH

noncomputable section

/-! The accepted integral H¹ crystalline equivalence, expressed on the
full ordinary product complex, has its literal finite reduction square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

private theorem inverse_of_hom {R : Type*} [CommRing R]
    {M N : ModuleCat R} (e : M ≅ N) (x : M) (y : N) (h : e.hom x = y) :
    e.inv y = x :=
  (congrArg e.inv h.symm).trans (ConcreteCategory.congr_hom e.hom_inv_id x)

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p])))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]

local notation "K" => HomologicalComplex₂.total
  (OrdinaryCechUnit.IntrinsicOrdinary.bicomplex p X) (ComplexShape.up ℕ)
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X
local notation "C" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.complex ℤ_[p] X U

theorem source_coordinates (n : ℕ) (x : (K).homology 1) :
    (GeometricComparison.IntrinsicPadic.FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X n).inv
      (GeometricComparison.IntrinsicPadic.IntegralReductionCoordinates.IntrinsicPadicIntegralReductionCoordinates.reduction p X (n+1)
        (PadicOne.IntrinsicH.globalEquiv p X x)) =
    HomologicalComplex.homologyMap (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.fullOpenIso p X n).inv 1
      (OrdinaryReduction.IntrinsicOrdinary.reduction p X n 1 x) := by
  have hc := inverse_of_hom (GeometricComparison.IntrinsicPadic.FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X n)
    (HomologicalComplex.homologyMap (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.fullOpenIso p X n).inv 1
      (OrdinaryReduction.IntrinsicOrdinary.reduction p X n 1 x))
    (GeometricComparison.CochainQuotientCohomology.PrincipalCochainQuotient.reduction ℤ_[p] C (p : ℤ_[p]) (n+1) 1
      ((PadicOne.IntrinsicH.cohomologyIso p X).hom x))
    (PadicOne.IntrinsicHReduction.coordinates p X n x)
  exact (congrArg
    (fun z => (GeometricComparison.IntrinsicPadic.FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X n).inv
      (GeometricComparison.CochainQuotientCohomology.PrincipalCochainQuotient.reduction ℤ_[p] C (p : ℤ_[p]) (n+1) 1 z))
    (PadicOne.IntrinsicH.global_coordinates p X x)).trans hc

variable (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsProper Y.hom] [Smooth Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (I : InjectiveResolution (BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (Witt.Crystalline.wittStructureMap p (ZMod p) Y)))
  (hprojective : Projectivity.Construction.ProjectiveOver (ZMod p) Y.hom)

def equiv := (PadicOne.IntrinsicH.globalEquiv p X).trans
  (GeometricComparison.IntrinsicPadic.IntegralCrystallineEquiv.IntrinsicPadicIntegralCrystallineEquiv.equiv p X Y f hp I hprojective)

theorem square (n : ℕ) (x : (K).homology 1) :
    GeometricComparison.IntrinsicPadic.CrystallineRestrictionExt.IntrinsicPadicIntegralCrystallineReduction.restriction p Y n
        (equiv p X Y f hp I hprojective x) =
      SmallCohomology.Intrinsic.linearEquiv p X Y f hp I n 1
        (HomologicalComplex.homologyMap (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.fullOpenIso p X n).inv 1
          (OrdinaryReduction.IntrinsicOrdinary.reduction p X n 1 x)) :=
  (SmallReductionSquare.Intrinsic.square p X Y f hp I hprojective n
    (PadicOne.IntrinsicH.globalEquiv p X x)).trans
    (congrArg (SmallCohomology.Intrinsic.linearEquiv p X Y f hp I n 1)
      (source_coordinates p X n x))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.OneCrystalline.IntrinsicH
