import OAI.AlgebraicGeometry.Picard.ThetaConstruction.Points
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomogeneousPointClass

/-! # Complex Bijection -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! The descended theta family identifies the complex points of the
constructed dual with the sections of the original homogeneous Picard
sheaf at Spec C. This uses actual algebraic fiber isomorphisms and the
actual sheafification map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomogeneousPointClass

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim}
    {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix} {hP : matrix.transpose = -matrix}
    {M : PeriodModel.Geometric.AlgebraicPeriodModel F} {D : IntegralDualModel.Geometric.IntegralDualAlgebraicModel F}
    (p : IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny M D)
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP)) (hdeg : V.degree = U.degree + 1)
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))
    (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (D.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
    (recover : (Q.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
      (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)).sheaf)
    (hQ : M.abelianScheme.IsHomogeneousPicardClass D.abelianScheme.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q))

include hdeg hf hg recover in
theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.exists_descendedTheta_pointFamilyClass
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⊗ M.abelianScheme.scheme).left)
    (hL : M.abelianScheme.IsHomogeneousPicardClass (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) :
    ∃ x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.abelian.toOver,
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.pullback (x ⊗ₘ 𝟙 M.abelianScheme.scheme).left) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L := by
  let L₀ := L.pullback (AbelianModuli.ReferenceFamily.IntrinsicPointLine.nativePointUnitIso M.abelianScheme.scheme).hom.left
  have he : AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily M.abelianScheme (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L₀) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L :=
    AbelianModuli.ReferenceFamily.IntrinsicPointLine.nativePointUnit_class_recovery M.abelianScheme.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)
  have hL₀ : AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety M.abelian) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L₀) := by
    change M.abelianScheme.IsHomogeneousPicardClass (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))
      (AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily M.abelianScheme (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L₀))
    rw [he]
    exact hL
  obtain ⟨x, hx, _⟩ := p.homogeneousLineBundle_unique_algebraic_parameter U V hdeg f g hf hg Q recover L₀ hL₀
  refine ⟨x, (AbelianModuli.ReferenceFamily.IntrinsicPointLine.nativePointFamilyLine_constant_recovery Q x).symm.trans ?_⟩
  exact (congrArg (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (snd (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) M.abelianScheme.scheme).left)
    (Quotient.sound hx)).trans he

include hdeg hf hg recover in
theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.nativeHomogeneousPointPicardClass_bijective :
    Function.Bijective (AbelianModuli.ReferenceFamily.Intrinsic.HomogeneousPointClass.nativeHomogeneousPointPicardClass M.abelianScheme Q hQ) := by
  constructor
  · intro x y h
    have hr := (AbelianModuli.ReferenceFamily.Intrinsic.HomogeneousPointClass.nativeHomogeneousPointPicardClass_eq_iff M.abelianScheme Q hQ x y).mp h
    have hc := congrArg (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (AbelianModuli.ReferenceFamily.IntrinsicPointLine.nativePointUnitIso M.abelianScheme.scheme).hom.left) hr
    rw [AbelianModuli.ReferenceFamily.IntrinsicPointLine.nativePointFamilyLine_parameter_pullback, AbelianModuli.ReferenceFamily.IntrinsicPointLine.nativePointFamilyLine_parameter_pullback] at hc
    exact p.descendedThetaHolomorphicClass_injective U V hdeg f g hf hg Q recover
      (congrArg (AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicIsoClass.nativeHolomorphicPicardClass M.abelian.variety) hc)
  · intro q
    obtain ⟨r, hr⟩ := (AbelianModuli.ReferenceFamily.ClosedSheafification.fppf_toSheafify_bijective_at_algClosed (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)
      M.abelianScheme.homogeneousPicardPresheaf).surjective q
    obtain ⟨L, hL⟩ := Quotient.exists_rep r.val
    have hh : M.abelianScheme.IsHomogeneousPicardClass (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) :=
      (congrArg (fun q => M.abelianScheme.IsHomogeneousPicardClass (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q) hL).mpr
        r.property
    obtain ⟨x, hx⟩ := p.exists_descendedTheta_pointFamilyClass U V hdeg f g hf hg Q recover L hh
    refine ⟨x, ?_⟩
    exact (congrArg ((toSheafify (Scheme.fppfTopology.over Foundations.Scheme.ProjectiveSpace.complexBase)
      M.abelianScheme.homogeneousPicardPresheaf).app (.op (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))))
        (show AbelianModuli.ReferenceFamily.Intrinsic.HomogeneousPointClass.nativeHomogeneousPointFamilyClass M.abelianScheme Q hQ x = r from
          Subtype.ext (hx.trans hL))).trans hr

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
