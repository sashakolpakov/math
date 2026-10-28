import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ClassScalarOn
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ClassKernel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructureComplexScalars

/-! # Class Scalar Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ClassScalarCompatibility

noncomputable section

/-! Scalar pullback on actual line families and their reduction
kernel preserves the original algebraic H1 complex scalar action. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] [IsReduced X.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]

theorem dualLineDeformationClass_scalar (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left) (c : ℂ) :
    let := StructureComplexScalars.structureH1ComplexModule X
    DeformationClass.dualLineDeformationClass X (L.pullback (Dual.Scalars.dualFamilyScalar X c).left) (Dual.ScalarFramePullback.dualScalarReductionFrame X L e₀ c) =
      c • DeformationClass.dualLineDeformationClass X L e₀ := by
  let := StructureComplexScalars.structureH1ComplexModule X
  let s := Dual.NormalizedFrameCover.normalizedDualFrameAt X L e₀
  let t (i : X.left) := (s i).scalarPullback X L e₀ c
  exact (FrameIndependence.dualLineDeformationClass_eq_frames X (L.pullback (Dual.Scalars.dualFamilyScalar X c).left)
    (Dual.ScalarFramePullback.dualScalarReductionFrame X L e₀ c) t (Dual.NormalizedFrameCover.normalizedDualFrameCover_base X L e₀)).trans
      (ClassScalarOn.normalizedDualFrameClass_scalar X L e₀ s (Dual.NormalizedFrameCover.normalizedDualFrameCover_base X L e₀) c)

theorem dualLineKernelCohomology_scalar (c : ℂ) (q : ClassKernel.dualLineClassKernel X) :
    let := StructureComplexScalars.structureH1ComplexModule X
    ClassKernel.dualLineKernelCohomology X (KernelScalarPullback.dualLineKernelScalar X c q) = c • ClassKernel.dualLineKernelCohomology X q := by
  let := StructureComplexScalars.structureH1ComplexModule X
  let L := ClassKernel.dualLineKernelRepresentative X q
  let e := ClassKernel.dualLineKernelFrame X q
  have h : HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (Dual.Scalars.dualFamilyScalar X c).left) = (KernelScalarPullback.dualLineKernelScalar X c q).val :=
    congrArg (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Dual.Scalars.dualFamilyScalar X c).left) (ClassKernel.dualLineKernelRepresentative_class X q)
  exact (ClassKernel.dualLineKernelCohomology_rep X (KernelScalarPullback.dualLineKernelScalar X c q) (L.pullback (Dual.Scalars.dualFamilyScalar X c).left)
    (Dual.ScalarFramePullback.dualScalarReductionFrame X L e c) h).trans (dualLineDeformationClass_scalar X L e c)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ClassScalarCompatibility
