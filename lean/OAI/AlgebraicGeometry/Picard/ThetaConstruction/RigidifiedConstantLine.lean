import OAI.AlgebraicGeometry.Picard.ThetaConstruction.GenericLineHomogeneityReflection
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeNormalizationFibers

/-! # Rigidified Constant Line -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RigidifiedConstantLine.Geometric

noncomputable section

/-! Identity normalization constructs an actual rigidified constant
family over each original test. Its relative Picard value is that of
the unnormalized original line, on every further test. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)

def relativeRigidifiedConstant (U : Over S) : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A.scheme U where
  bundle := (RelativeDifferenceBundle.Geometric.identityNormalizedLine A L).pullback (snd U A.scheme).left
  axis := by
    have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (((RelativeDifferenceBundle.Geometric.identityNormalizedLine A L).pullback (snd U A.scheme).left).pullback
        (lift (𝟙 U) (1 : U ⟶ A.scheme)).left) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass U.left := by
      change RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (lift (𝟙 U) (1 : U ⟶ A.scheme)).left
        (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (snd U A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))) = 1
      rw [RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback_comp]
      have hs : (lift (𝟙 U) (1 : U ⟶ A.scheme)).left ≫ (snd U A.scheme).left =
          (1 : U ⟶ A.scheme).left := congrArg Over.Hom.left (lift_snd (𝟙 U) (1 : U ⟶ A.scheme))
      rw [hs]
      exact RelativeCubeClasses.Geometric.identityNormalizedLine_one_class A L U
    exact Classical.choice (Quotient.exact hc)

theorem relativeRigidifiedConstant_value {U V : Over S} (a : V ⟶ U) :
    (relativeRigidifiedConstant A L U).relativeValue a =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op V)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd V A.scheme).left)) := by
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op V)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (a ⊗ₘ 𝟙 A.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd U A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)))) = _
  have hs : (a ⊗ₘ 𝟙 A.scheme).left ≫ (snd U A.scheme).left = (snd V A.scheme).left :=
    (congrArg Over.Hom.left (tensorHom_snd a (𝟙 A.scheme))).trans (Category.comp_id _)
  have hp := (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (a ⊗ₘ 𝟙 A.scheme).left
    (snd U A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))).symm.trans
      (congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))) hs)
  exact (congrArg (fun q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (V ⊗ A.scheme).left =>
    Homomorphisms.RelativeGroup.Construction.toRelativePicardHom A.scheme V q) hp).trans
      (ReferenceLineTranslation.Geometric.originalLineFamily_picard_normalization A L V)

variable [IsAffine S] [IsLocalRing Γ(S, ⊤)] [IsNoetherianRing Γ(S, ⊤)]
    [IsLocallyNoetherian S] [IsIntegral S]

theorem relativeRigidifiedConstant_homogeneous_of_generic
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (hL : AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass (A.pullback (S.fromSpecResidueField (genericPoint S)))
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (A.scheme.hom.fiberι (genericPoint S)))))
    (U : Over S) :
    A.IsHomogeneousPicardClass U (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (relativeRigidifiedConstant A L U).bundle) := by
  have hN : AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass (A.pullback (S.fromSpecResidueField (genericPoint S)))
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((RelativeDifferenceBundle.Geometric.identityNormalizedLine A L).pullback
        (A.scheme.hom.fiberι (genericPoint S)))) := by
    have hc := RelativeNormalizationFibers.Geometric.identityNormalizedLine_fieldPullback_class A L
      (A.scheme.hom.fiberι (genericPoint S)) (A.scheme.hom.fiberToSpecResidueField (genericPoint S))
      (S.fromSpecResidueField (genericPoint S)) CategoryTheory.Limits.pullback.condition
    exact (congrArg (fun q => AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass
      (A.pullback (S.fromSpecResidueField (genericPoint S))) q) hc).mpr hL
  exact GenericLineHomogeneityReflection.Geometric.constantFamily_homogeneous_of_generic A P (RelativeDifferenceBundle.Geometric.identityNormalizedLine A L) hN U

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RigidifiedConstantLine.Geometric
