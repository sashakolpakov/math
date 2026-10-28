import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructureSheafScalarPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PushforwardCohomologyNaturality

/-! # Structure Pullback Linear -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructurePullbackLinear

noncomputable section

/-! Pullback on the actual native structure-sheaf H1 is complex
linear for the scalar actions coming from the original complex base
morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] StructurePullback.nativeStructureH1_group

local instance structureH1Pullback_complexModule (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule X.left) 1) := StructureComplexScalars.structureH1ComplexModule X

theorem structureAdditiveScalar_H1 (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (c : ℂ)
    (x : SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule X.left) 1) :
    CategoryTheory.Sheaf.H.map (StructureSheafScalarPullback.structureAdditiveScalar X c) 1 x = c • x := rfl

theorem nativeStructureH1Pullback_smul {A B : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : A ⟶ B) (c : ℂ)
    (x : SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule B.left) 1) :
    StructurePullback.nativeStructureH1Pullback f (c • x) = c • StructurePullback.nativeStructureH1Pullback f x := by
  have hh := congrArg (fun q => CategoryTheory.Sheaf.H.map q 1 x) (StructureSheafScalarPullback.structureAdditiveScalar_pullback f c)
  have hl := CategoryTheory.Sheaf.H.map_comp_apply (StructureSheafScalarPullback.structureAdditiveScalar B c) (StructurePullback.structureAdditivePullbackHom f.left)
    (show CategoryTheory.Sheaf.H (Dual.UnitCechClasses.ringAdditiveSheaf B.left.sheaf) 1 from x)
  have hr := CategoryTheory.Sheaf.H.map_comp_apply (StructurePullback.structureAdditivePullbackHom f.left)
    ((ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPushforward f.left.base).map (StructureSheafScalarPullback.structureAdditiveScalar A c))
    (show CategoryTheory.Sheaf.H (Dual.UnitCechClasses.ringAdditiveSheaf B.left.sheaf) 1 from x)
  have hh' := hl.symm.trans (hh.trans hr)
  have hn := PushforwardCohomologyNaturality.abelianPushforwardCohomologyMap_natural f.left.base (StructureSheafScalarPullback.structureAdditiveScalar A c) 1
    (CategoryTheory.Sheaf.H.map (StructurePullback.structureAdditivePullbackHom f.left) 1 x)
  rw [← structureAdditiveScalar_H1 B c x,
    ← structureAdditiveScalar_H1 A c (StructurePullback.nativeStructureH1Pullback f x)]
  exact (congrArg (ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardCohomology.Construction.abelianPushforwardCohomologyMap f.left.base (Dual.UnitCechClasses.ringAdditiveSheaf A.left.sheaf) 1) hh').trans hn

def nativeStructureH1PullbackLinear {A B : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : A ⟶ B) :
    SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule B.left) 1 →ₗ[ℂ] SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.left) 1 where
  toFun := StructurePullback.nativeStructureH1Pullback f
  map_add' := (StructurePullback.nativeStructureH1Pullback f).map_add
  map_smul' := nativeStructureH1Pullback_smul f

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructurePullbackLinear
