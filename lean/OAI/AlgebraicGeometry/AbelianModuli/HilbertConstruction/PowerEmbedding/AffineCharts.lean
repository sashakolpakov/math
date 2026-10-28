import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.ProjectiveEmbeddings
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Preimages
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StandardProjectiveCharts
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Affine Charts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every section chart in an actual power projective embedding over an affine base is affine. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (p : X ⟶ S) [IsAffine S] {L : Line.Bundles.LineBundle X}

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.absolute_closedImmersion (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L p) :
    IsClosedImmersion (SectionsProjectiveMorphism.sectionAbsoluteMorphism p E.sections E.covers) := by
  let j := SectionsProjectiveMorphism.sectionProjectiveMorphism p E.sections E.covers
  let q := Limits.pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) E.dimension).hom S.toSpecΓ
  have hj : IsClosedImmersion j.left := E.closedImmersion
  have : IsIso q := inferInstanceAs
    (IsIso (Limits.pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) E.dimension).hom S.toSpecΓ))
  have h : j.left ≫ q = SectionsProjectiveMorphism.sectionAbsoluteMorphism p E.sections E.covers := Limits.pullback.lift_fst _ _ _
  have hq : IsClosedImmersion q := inferInstance
  exact h ▸ @IsClosedImmersion.comp _ _ _ j.left q hj hq

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.sectionChart_isAffine (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L p)
    (i : Fin (E.dimension + 1)) : IsAffineOpen (Ample.LineBundles.sectionNonvanishing (E.sections i)) := by
  let f := SectionsProjectiveMorphism.sectionAbsoluteMorphism p E.sections E.covers
  have hc : IsClosedImmersion f := E.absolute_closedImmersion p
  have hf : IsAffineHom f := isAffineHom_of_isInducing f
    hc.isClosedEmbedding.isInducing hc.isClosedEmbedding.isClosed_range
  have h := @IsAffineOpen.preimage _ _ _
    (StandardProjectiveCharts.standardProjectiveChart_isAffine Γ(S, ⊤) E.dimension i) f hf
  exact (ProjectiveChart.Preimages.sectionAbsoluteMorphism_preimage p E.sections E.covers i) ▸ h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
