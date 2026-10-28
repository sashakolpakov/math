import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.LineBundleTrivialization
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Scheme Finite Type -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! Over a Noetherian base the open frame scheme is quasi-compact, so
the derived trivialization scheme is of finite type. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u
section

variable {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  {π : X ⟶ S} [IsProper π] {L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X}
  (D : Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π L.sheaf)

instance Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.frameScheme_quasiCompact : QuasiCompact D.frameSchemeOverBase.hom := by
  have : Algebra.FiniteType Γ(S, ⊤) D.algebra := D.finiteType
  have : IsNoetherianRing D.algebra := Algebra.FiniteType.isNoetherianRing Γ(S, ⊤) D.algebra
  have : NoetherianSpace D.scheme.left := inferInstanceAs (NoetherianSpace (Spec (CommRingCat.of D.algebra)))
  have : NoetherianSpace D.frameOpen.toScheme := D.frameOpen.ι.isOpenEmbedding.isInducing.noetherianSpace
  change QuasiCompact (D.frameOpen.ι ≫ D.scheme.hom)
  infer_instance

end

instance Frame.SchemeFiniteType.Construction.projectiveLineBundleFrameScheme_quasiCompact
    {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (X : Over S) (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) [Flat X.hom] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) :
    QuasiCompact (Projective.LineBundleSectionScheme.Construction.projectiveLineBundleFrameScheme X P L).hom := by
  have : IsProper X.hom := P.proper
  exact (Projective.LineBundleSectionScheme.Construction.projectiveLineBundleSectionModel X P L).frameScheme_quasiCompact

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion
