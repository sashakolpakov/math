import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GeometricallyAmpleSectionMorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SectionMorphismAmpleness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.ProjectivePresentation

/-! # Geometric Ampleness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Over an affine base, a finite generating family and ampleness on geometric fibers imply actual ampleness and a projective presentation of a proper scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S X : Scheme.{u}} [IsAffine S] (f : X ⟶ S) [IsProper f] (L : Line.Bundles.LineBundle X) {n : ℕ}
variable (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
variable (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
variable (hL : ∀ (K : Type u) [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ S),
  (L.pullback (Limits.pullback.fst f b)).IsAmple)

include hs hL

theorem Generated.GeometricAmpleness.sectionAbsoluteMorphism_isFinite_of_geometric_ample :
    IsFinite (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) := by
  let a := SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs
  let p := Limits.pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ
  have ha : IsFinite a.left := GeometricallyAmpleSectionMorphism.sectionProjectiveMorphism_isFinite_of_geometric_ample f L s hs hL
  have : IsIso p := inferInstanceAs
    (IsIso (Limits.pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ))
  have hpFinite : IsFinite p := inferInstance
  have h : IsFinite (a.left ≫ p) := MorphismProperty.comp_mem (@IsFinite) _ _ ha hpFinite
  have hp : a.left ≫ p = SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs := Limits.pullback.lift_fst _ _ _
  exact hp ▸ h

theorem Line.Bundles.LineBundle.isAmple_of_geometric_fibers_of_generating_sections : L.IsAmple := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsFinite (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) :=
    Generated.GeometricAmpleness.sectionAbsoluteMorphism_isFinite_of_geometric_ample f L s hs hL
  exact L.isAmple_of_affine_sectionMorphism f s hs

def Line.Bundles.LineBundle.projectivePresentation_of_geometric_fibers_of_generating_sections :
    Projective.ProjectivePresentations.ProjectivePresentation (Over.mk f) :=
  (L.isAmple_of_geometric_fibers_of_generating_sections f s hs hL).projectivePresentation f

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
