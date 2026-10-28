import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveGlobalLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GlobalHomologyFactors
import OAI.NumberTheory.PadicHodge.GeometricComparison.FactorEquality

/-! # Injective Bicomplex Level Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveBicomplexLevelCoordinates.IntrinsicPadicInjectiveBicomplexLevelCoordinates

noncomputable section

/-! The original level and finite injective comparisons use the
same bicomplex isomorphism before totalization and homology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y))) (n : ℕ)

local notation "Iq" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution
  (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n I

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))

omit [IsSeparated Y.hom] in
theorem bicomponent (q r : ℕ) :
    ((InjectiveCechLevel.IntrinsicPadicInjectiveCechLevel.comparisonIso p X Y f I n).hom.f q).f r =
      ((InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.bicomplexIso p X Y f n Iq).hom.f q).f r := rfl

omit [IsSeparated Y.hom] in
theorem row (q : ℕ) : (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevel.comparisonIso p X Y f I n).hom.f q =
    (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.bicomplexIso p X Y f n Iq).hom.f q := by
  apply HomologicalComplex.Hom.ext
  funext r
  exact bicomponent p X Y f I n q r

omit [IsSeparated Y.hom] in
theorem bicomplex_hom : (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevel.comparisonIso p X Y f I n).hom =
    (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.bicomplexIso p X Y f n Iq).hom := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact row p X Y f I n q

omit [IsSeparated Y.hom] in
theorem bicomplex_iso : InjectiveCechLevel.IntrinsicPadicInjectiveCechLevel.comparisonIso p X Y f I n =
    InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.bicomplexIso p X Y f n Iq :=
  Iso.ext (bicomplex_hom p X Y f I n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveBicomplexLevelCoordinates.IntrinsicPadicInjectiveBicomplexLevelCoordinates
