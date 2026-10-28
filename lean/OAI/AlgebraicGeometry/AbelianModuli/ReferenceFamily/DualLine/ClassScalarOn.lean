import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ScalarCechCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ScalarFramePullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.FrameIndependence
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.DualClassScalars

/-! # Class Scalar On -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ClassScalarOn

noncomputable section

/-! Scalar pullback of a normalized affine line-family atlas uses
the original global-sections scalar action on its algebraic H1 class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory

theorem normalizedDualFrameClass_scalar (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] [IsReduced X.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]
    (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left)
    {I : Type} (s : I → Dual.NormalizedFrameCover.NormalizedDualFrame X L e₀) (hs : iSup (fun i => (s i).baseOpen X L e₀) = ⊤) (c : ℂ) :
    let : Module Γ(X.left, ⊤) (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule X.left) 1) :=
      SheafCohomology.AffineH.Projective.globalSectionsCohomologyModule (HilbertConstruction.Line.Bundles.structureModule X.left) 1
    DeformationClass.normalizedDualFrameClass X (L.pullback (Dual.Scalars.dualFamilyScalar X c).left) (Dual.ScalarFramePullback.dualScalarReductionFrame X L e₀ c)
      (fun i => (s i).scalarPullback X L e₀ c) hs =
        Open.ComplexConstants.complexGlobalSectionMap X c • DeformationClass.normalizedDualFrameClass X L e₀ s hs := by
  let : Module Γ(X.left, ⊤) (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule X.left) 1) :=
    SheafCohomology.AffineH.Projective.globalSectionsCohomologyModule (HilbertConstruction.Line.Bundles.structureModule X.left) 1
  let K := L.pullback (Dual.Scalars.dualFamilyScalar X c).left
  let d := Dual.ScalarFramePullback.dualScalarReductionFrame X L e₀ c
  let t (i : I) := (s i).scalarPullback X L e₀ c
  refine Regular.DualClassScalars.regularDualUnitClass_scalar X.left (fun i => (s i).baseOpen X L e₀) hs
    (LineFrameDualCech.lineFrameDualCech X (fun i => (s i).localFrame X L e₀) (fun i => (s i).affine))
    (LineFrameDualCech.lineFrameDualCech X (fun i => (t i).localFrame X K d) (fun i => (s i).affine))
    (NormalizedDual.Cech.normalizedDualFrames_cech X L e₀ s) (NormalizedDual.Cech.normalizedDualFrames_cech X K d t)
    (LineFrameDualCech.lineFrameDualCech_cocycle X (fun i => (s i).localFrame X L e₀) (fun i => (s i).affine))
    (LineFrameDualCech.lineFrameDualCech_cocycle X (fun i => (t i).localFrame X K d) (fun i => (s i).affine))
    (Open.ComplexConstants.complexGlobalSectionMap X c) ?_
  intro a
  exact Dual.ScalarCechCoefficients.lineFrameDualCech_scalar X L.sheaf (fun i => (s i).domain) (fun i => (s i).affine) (fun i => (s i).frame) a c

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ClassScalarOn
