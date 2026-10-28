import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.TranslationRigidity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel
import OAI.RepresentationTheory.Theta.Geometric.PointDifferenceHomomorphism
import OAI.RepresentationTheory.Theta.Geometric.Cubical.ClassPullback

/-! # Point Difference -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! The kernel of the native reference difference-class homomorphism
is contained in the actual lattice-isogeny kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}

def AlgebraicModel.ReferenceAlgebraicModel.pointDifferenceHom (M : AlgebraicModel.ReferenceAlgebraicModel F hP)
    (L : HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left)
    (hcube : RepresentationTheory.Theta.Geometric.Intrinsic.CubeClass.nativeCubeDefect M.abelian (HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver →* HilbertConstruction.Line.Bundles.LineBundle.IsoClass M.abelian.toOver.left where
  toFun := RepresentationTheory.Theta.Geometric.PointBundleClasses.pointBundleClass (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme L)
  map_one' := RepresentationTheory.Theta.Geometric.PointDifferenceHomomorphism.pointDifferenceBundle_class_one M.abelianScheme L
  map_mul' := RepresentationTheory.Theta.Geometric.PointDifferenceHomomorphism.pointDifferenceBundle_class_mul M.abelianScheme L
    (fun _ a b c => RepresentationTheory.Theta.Geometric.Cubical.ClassPullback.nativeCubeClass_pullback M.abelian (HilbertConstruction.Line.Bundles.LineBundle.classOf L) hcube a b c)

variable {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {D : DualModel.ReferenceDualModel F hP}
    (p : IsogenyKernel.ReferenceLatticeIsogeny M D)

theorem IsogenyKernel.ReferenceLatticeIsogeny.complexPoints_surjective : Function.Surjective (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.isogeny.hom) := by
  intro y
  obtain ⟨t, rfl⟩ := D.period.surjective y
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t
  exact ⟨M.period (QuotientAddGroup.mk w), p.period_eq (QuotientAddGroup.mk w)⟩

theorem IsogenyKernel.ReferenceLatticeIsogeny.pointDifference_eq_one_mem_kernel
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP)) (hdeg : V.degree = U.degree + 1)
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))
    (a : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (ha : RepresentationTheory.Theta.Geometric.PointBundleClasses.pointBundleClass (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)) a = 1) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.isogeny.hom a = 1 := by
  obtain ⟨t, rfl⟩ := M.period.surjective a
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t
  have H := (RepresentationTheory.Theta.Geometric.PointBundleClasses.pointDifferenceBundle_class M.abelianScheme
    (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left) (M.period (QuotientAddGroup.mk w))).symm.trans ha
  have H' : RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (RepresentationTheory.Theta.Geometric.AlgebraicTranslation.abelianTranslation M.abelian (M.period (QuotientAddGroup.mk w))).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)) =
    HilbertConstruction.Line.Bundles.LineBundle.classOf (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left) := mul_inv_eq_one.mp H
  obtain ⟨u⟩ := Quotient.exact H'
  have hw := M.nativeTranslation_mem_dual U V hdeg f g hf hg w u
  have hzero : F.latticeTorusMap hP (QuotientAddGroup.mk w) = 0 :=
    (F.dualPeriodQuotient_eq_zero hP w).mpr hw
  exact (p.period_eq (QuotientAddGroup.mk w)).trans ((congrArg D.period hzero).trans
    (congrArg Additive.toMul D.periodAddEquiv.map_zero))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
