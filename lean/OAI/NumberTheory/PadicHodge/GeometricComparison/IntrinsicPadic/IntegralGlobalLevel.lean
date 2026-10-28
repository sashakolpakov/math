import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveGlobalLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCechLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechMapCoordinates

/-! # Integral Global Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralGlobalLevel.IntrinsicPadicIntegralGlobalLevel

noncomputable section

/-! The canonical finite-level integral quotient Cech H-one comparison
with original global crystalline cohomology respects level transitions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n m : ℕ) (hnm : n ≤ m)
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y)))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "Iq" => fun q : ℕ => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution wittMap q I
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X)

def homologyIso (q : ℕ) :
    IntegralCechLevel.IntrinsicPadicIntegralCechLevel.sourceHOne p X q ≅
    ModuleCat.of R (IntegralComparison.BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : WittVector p (ZMod p))})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) wittMap q 1) :=
  letI : QuasiIsoAt (IntegralCechLevel.IntrinsicPadicIntegralCechLevel.comparisonMap p X Y f hp I q) 1 :=
    IntegralCechOne.IntrinsicPadicIntegralCechHOne.quasiIsoAt p X Y f hp q (Iq q)
  isoOfQuasiIsoAt (IntegralCechLevel.IntrinsicPadicIntegralCechLevel.comparisonMap p X Y f hp I q) 1 ≪≫
    InjectiveGlobalLevel.IntrinsicPadicInjectiveGlobalLevel.homologyIso p X Y f I q 1

theorem homologyIso_hom (q : ℕ) : (homologyIso p X Y f hp I q).hom =
    IntegralCechLevel.IntrinsicPadicIntegralCechLevel.comparisonHOne p X Y f hp I q ≫
      (InjectiveGlobalLevel.IntrinsicPadicInjectiveGlobalLevel.homologyIso p X Y f I q 1).hom := rfl

omit [IsSeparated Y.hom] in
theorem target_natural : IntegralCechLevel.IntrinsicPadicIntegralCechLevel.targetHOneMap p X Y f n m hnm I ≫
    (InjectiveGlobalLevel.IntrinsicPadicInjectiveGlobalLevel.homologyIso p X Y f I n 1).hom =
      (InjectiveGlobalLevel.IntrinsicPadicInjectiveGlobalLevel.homologyIso p X Y f I m 1).hom ≫
        ModuleCat.ofHom (IntegralComparison.Bounded.CohomologyTransition.map wittMap n m hnm 1) := by
  let H := fun (a : IntegralCechLevel.IntrinsicPadicIntegralCechLevel.target p X Y f I m ⟶
      IntegralCechLevel.IntrinsicPadicIntegralCechLevel.target p X Y f I n) => HomologicalComplex.homologyMap a 1
  exact (congrArg (fun a => a ≫ (InjectiveGlobalLevel.IntrinsicPadicInjectiveGlobalLevel.homologyIso p X Y f I n 1).hom)
    (congrArg H (InjectiveCechMapCoordinates.IntrinsicPadicInjectiveCechMapCoordinates.total p X Y f n m hnm I))).trans
      (InjectiveGlobalLevel.IntrinsicPadicInjectiveGlobalLevel.homology p X Y f n m hnm I 1)

theorem natural : IntegralCechLevel.IntrinsicPadicIntegralCechLevel.sourceHOneMap p X n m hnm ≫
    (homologyIso p X Y f hp I n).hom =
      (homologyIso p X Y f hp I m).hom ≫ ModuleCat.ofHom (IntegralComparison.Bounded.CohomologyTransition.map wittMap n m hnm 1) := by
  have h := ExactHomology.ExactHomologyComparison.compose
    (IntegralCechLevel.IntrinsicPadicIntegralCechLevel.sourceHOneMap p X n m hnm)
    (IntegralCechLevel.IntrinsicPadicIntegralCechLevel.comparisonHOne p X Y f hp I n)
    (InjectiveGlobalLevel.IntrinsicPadicInjectiveGlobalLevel.homologyIso p X Y f I n 1).hom
    (IntegralCechLevel.IntrinsicPadicIntegralCechLevel.comparisonHOne p X Y f hp I m)
    (IntegralCechLevel.IntrinsicPadicIntegralCechLevel.targetHOneMap p X Y f n m hnm I)
    (InjectiveGlobalLevel.IntrinsicPadicInjectiveGlobalLevel.homologyIso p X Y f I m 1).hom
    (ModuleCat.ofHom (IntegralComparison.Bounded.CohomologyTransition.map wittMap n m hnm 1))
    (IntegralCechLevel.IntrinsicPadicIntegralCechLevel.homology p X Y f hp n m hnm I).symm
    (target_natural p X Y f n m hnm I)
  exact (congrArg (fun a => IntegralCechLevel.IntrinsicPadicIntegralCechLevel.sourceHOneMap p X n m hnm ≫ a)
    (homologyIso_hom p X Y f hp I n)).trans
      (h.trans (congrArg (fun a => a ≫ ModuleCat.ofHom (IntegralComparison.Bounded.CohomologyTransition.map wittMap n m hnm 1))
        (homologyIso_hom p X Y f hp I m).symm))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralGlobalLevel.IntrinsicPadicIntegralGlobalLevel
