import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeLocalEquations
import OAI.RepresentationTheory.Theta.Geometric.Affine.QuotientFlatness
import OAI.RepresentationTheory.Theta.Geometric.Affine.QuotientSpecProjection

/-! # Relative Local Flatness -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeLocalFlatness.Geometric.RelativeRigidifiedCharts

noncomputable section

/-! The constructed local equations prove flatness of the actual Picard
comparison projection over the literal ring R when its fiber H1 is bounded by the ambient rank. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory KaehlerDifferential

variable {S : Scheme} {A B T : Over S} [GrpObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [IsLocallyNoetherian B.left] (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A) (D : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B)
    [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)] [IsLocalRing Γ(T.left, ⊤)]
    [IsLocallyNoetherian T.left]
    (a : T ⟶ B) {R : Type} [CommRing R] (p : T.left ⟶ Spec (.of R))

theorem zeroScheme_local_toSpec_flat
    [FormallyUnramified ((RepresentationTheory.Theta.Geometric.SubobjectPullbackPoints.subobjectPullback (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P) a.left).hom ≫ p)]
    (eM : (Scheme.Modules.pullback ((FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom.fiberι
      (RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint T.left))).obj (D.line a).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom.fiber (RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint T.left))) :
    letI : Algebra R Γ(T.left, ⊤) := (FormalGeometry.Completion.Affine.BaseAlgebraPoints.Construction.globalRingPointEquiv T.left (.of R) p).toAlgebra
    ∀ [Algebra.FormallySmooth R Γ(T.left, ⊤)] [Module.Flat R Γ(T.left, ⊤)]
      [Module.Free Γ(T.left, ⊤) Ω[Γ(T.left, ⊤)⁄R]]
      [Module.Finite Γ(T.left, ⊤) Ω[Γ(T.left, ⊤)⁄R]],
      RelativeProjectiveEquations.Geometric.relativeProjectiveClosedFiberH1 (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom
        (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyProjectivePresentation A T P) (D.line a) ≤
        Module.finrank Γ(T.left, ⊤) Ω[Γ(T.left, ⊤)⁄R] →
      Flat ((RepresentationTheory.Theta.Geometric.SubobjectPullbackPoints.subobjectPullback (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P) a.left).hom ≫ p) := by
  let : Algebra R Γ(T.left, ⊤) := (FormalGeometry.Completion.Affine.BaseAlgebraPoints.Construction.globalRingPointEquiv T.left (.of R) p).toAlgebra
  intro _ _ _ _ hdim
  obtain ⟨n, v, hn, hv, ⟨e⟩⟩ := RelativeLocalEquations.Geometric.RelativeRigidifiedCharts.exists_zeroScheme_local_equations P D a eM
  let I := Ideal.span (Set.range v)
  have hI : I ≠ ⊤ := by
    intro h
    exact (IsLocalRing.maximalIdeal.isMaximal Γ(T.left, ⊤)).ne_top
      (top_unique (h ▸ hv))
  have : FormallyUnramified ((RepresentationTheory.Theta.Geometric.Affine.QuotientPoints.affineQuotientScheme T.left I).hom ≫ p) :=
    RepresentationTheory.Theta.Geometric.Affine.QuotientFlatness.overIso_projection_formallyUnramified p _ _ e.symm
  have : Flat ((RepresentationTheory.Theta.Geometric.Affine.QuotientPoints.affineQuotientScheme T.left I).hom ≫ p) :=
    RepresentationTheory.Theta.Geometric.Affine.QuotientSpecProjection.affineQuotientProjection_toSpec_flat p I hI v rfl (hn ▸ hdim)
  exact RepresentationTheory.Theta.Geometric.Affine.QuotientFlatness.overIso_projection_flat p _ _ e

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeLocalFlatness.Geometric.RelativeRigidifiedCharts
