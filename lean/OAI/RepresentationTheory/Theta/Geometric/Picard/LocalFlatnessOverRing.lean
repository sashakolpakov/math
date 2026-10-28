import OAI.RepresentationTheory.Theta.Geometric.Picard.ZeroSchemeLocalEquations
import OAI.RepresentationTheory.Theta.Geometric.Affine.QuotientFlatness
import OAI.RepresentationTheory.Theta.Geometric.Affine.QuotientSpecProjection

/-! # Local Flatness Over Ring -/

namespace OAI.RepresentationTheory.Theta.Geometric.Picard.LocalFlatnessOverRing

noncomputable section

/-! The constructed local equations prove flatness of the actual Picard
comparison projection over the literal ring R when its fiber H1 is bounded by the ambient rank. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory KaehlerDifferential

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
    {A B T : Over (Spec (.of K))} [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
    [IsLocallyNoetherian B.left] (D : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A B)
    [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)] [IsLocalRing Γ(T.left, ⊤)]
    (a : T ⟶ B) {R : Type u} [CommRing R] (p : T.left ⟶ Spec (.of R))

theorem picard_zeroScheme_local_toSpec_flat
    [FormallyUnramified ((SubobjectPullbackPoints.subobjectPullback D.zeroScheme a.left).hom ≫ p)]
    (eM : (Scheme.Modules.pullback ((AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom.fiberι
      (Local.AxisCechChart.affineLocalClosedPoint T.left))).obj (D.line a).sheaf ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom.fiber (Local.AxisCechChart.affineLocalClosedPoint T.left))) :
    letI : Algebra R Γ(T.left, ⊤) := (AlgebraicGeometry.FormalGeometry.Completion.Affine.BaseAlgebraPoints.Construction.globalRingPointEquiv T.left (.of R) p).toAlgebra
    ∀ [Algebra.FormallySmooth R Γ(T.left, ⊤)] [Module.Flat R Γ(T.left, ⊤)]
      [Module.Free Γ(T.left, ⊤) Ω[Γ(T.left, ⊤)⁄R]]
      [Module.Finite Γ(T.left, ⊤) Ω[Γ(T.left, ⊤)⁄R]],
      Projective.PicardLocalEquations.projectiveClosedFiberH1 (AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom
        (AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.geometricGroupFamilyProjectivePresentation A T) (D.line a) ≤
        Module.finrank Γ(T.left, ⊤) Ω[Γ(T.left, ⊤)⁄R] →
      Flat ((SubobjectPullbackPoints.subobjectPullback D.zeroScheme a.left).hom ≫ p) := by
  let : Algebra R Γ(T.left, ⊤) := (AlgebraicGeometry.FormalGeometry.Completion.Affine.BaseAlgebraPoints.Construction.globalRingPointEquiv T.left (.of R) p).toAlgebra
  intro _ _ _ _ hdim
  obtain ⟨n, v, hn, hv, ⟨e⟩⟩ := ZeroSchemeLocalEquations.exists_picard_zeroScheme_local_equations D a eM
  let I := Ideal.span (Set.range v)
  have hI : I ≠ ⊤ := by
    intro h
    exact (IsLocalRing.maximalIdeal.isMaximal Γ(T.left, ⊤)).ne_top
      (top_unique (h ▸ hv))
  have : FormallyUnramified ((Affine.QuotientPoints.affineQuotientScheme T.left I).hom ≫ p) :=
    Affine.QuotientFlatness.overIso_projection_formallyUnramified p _ _ e.symm
  have : Flat ((Affine.QuotientPoints.affineQuotientScheme T.left I).hom ≫ p) :=
    Affine.QuotientSpecProjection.affineQuotientProjection_toSpec_flat p I hI v rfl (hn ▸ hdim)
  exact Affine.QuotientFlatness.overIso_projection_flat p _ _ e

end

end OAI.RepresentationTheory.Theta.Geometric.Picard.LocalFlatnessOverRing
