import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechGlobal

/-! # Global Homology Factors -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GlobalHomologyFactors.IntrinsicPadicGlobalHomologyFactors

noncomputable section

/-! Expose the two original factors of the native global homology
isomorphism without comparing it to another presentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left) (n : ℕ)
  (I : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X Y f
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.FlasqueComplex.complex w n I

local instance limits : HasLimitsOfSize.{0, 0} (ModuleCat.{2} R) := ModuleCat.hasLimitsOfSize.{0, 0, 2, 1}
local instance colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{2} R) := ModuleCat.hasColimitsOfSize.{2, 1, 0, 0} R

local instance tuple_preserves (m : ℕ) (t : Fin (m + 1) → Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X) :
    PreservesLimit (Discrete.functor (U ∘ t)) F := by
  dsimp only [SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens]
  infer_instance

omit [IsSeparated Y.hom] in
theorem homologyIso_hom (i : ℕ) : (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.homologyIso p X Y f n I i).hom =
    HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.mapIso (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.bicomplexIso p X Y f n I) (.up ℕ)).hom i ≫
        (Bounded.FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.homologyIso w n I
          (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.specialCover p X Y f) (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.cover p X Y f) i).hom := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GlobalHomologyFactors.IntrinsicPadicGlobalHomologyFactors
