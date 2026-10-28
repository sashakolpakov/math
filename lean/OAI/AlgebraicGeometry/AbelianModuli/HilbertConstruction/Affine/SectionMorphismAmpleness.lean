import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SectionMorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles

/-! # Section Morphism Ampleness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A generating family whose projective section morphism is affine proves ampleness of the original line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Line.Bundles.LineBundle.isAmple_of_affine_sectionMorphism
    {S X : Scheme.{u}} [CompactSpace X] (f : X ⟶ S) (L : Line.Bundles.LineBundle X) {n : ℕ}
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    [hf : IsAffineHom (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)] : L.IsAmple := by
  refine ⟨isCompact_univ, fun x => ?_⟩
  obtain ⟨i, hi⟩ := hs x
  refine ⟨1, Nat.zero_lt_one, L, Tensor.Powers.isTensorPower_one L.sheaf, s i, hi, ?_⟩
  have h := @IsAffineOpen.preimage _ _ _ (StandardProjectiveCharts.standardProjectiveChart_isAffine Γ(S, ⊤) n i)
    (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) hf
  exact (ProjectiveChart.Preimages.sectionAbsoluteMorphism_preimage f s hs i) ▸ h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
