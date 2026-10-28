import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LocalPolarizationEmbedding
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.BaseAmpleness

/-! # Polarization Embedding -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.PolarizationEmbedding

noncomputable section

/-! On an affine noetherian base, the actual canonical polarization
line is ample and supplies a constructed global closed section embedding. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem polarizationLine_isAmple_affine
    {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) :
    (Relative.PoincareSimilitude.RelativePoincareClasses.polarizationLine A.dual A.polarization.isogeny.hom).IsAmple := by
  let f := A.abelian.scheme.hom
  let L := Relative.PoincareSimilitude.RelativePoincareClasses.polarizationLine A.dual A.polarization.isogeny.hom
  have : A.abelian.scheme.left.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have : CompactSpace A.abelian.scheme.left := QuasiCompact.compactSpace_of_compactSpace f
  apply BaseAmpleness.isAmple_of_affine_base_neighborhoods f L
  intro x
  obtain ⟨U, hxU, _, hU⟩ := LocalPolarizationEmbedding.polarizationLine_exists_affine_ample_neighborhood A x
  obtain ⟨e⟩ := Quotient.exact (Relative.CMPolarizationLine.RelativePoincareClasses.polarizationLine_baseChange_class A.dual
    A.polarization.isogeny.hom U.ι)
  have hp : (L.pullback (pullback.fst f U.ι)).IsAmple := hU.of_iso e
  exact ⟨U, hxU, (Cartesian.SectionAmpleness.PolarizationEmbedding.isAmple_pullback_iff_of_cartesian f L (f ⁻¹ᵁ U).ι (f ∣_ U) U.ι
    (isPullback_morphismRestrict f U).flip).mpr hp⟩

theorem polarized_exists_affine_section_embedding
    {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) :
    ∃ d : ℕ, 0 < d ∧ ∃ L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.abelian.scheme.left,
      AbelianModuli.HilbertConstruction.Tensor.Powers.IsTensorPower (Relative.PoincareSimilitude.RelativePoincareClasses.polarizationLine A.dual A.polarization.isogeny.hom).sheaf d L.sheaf ∧
      ∃ (n : ℕ) (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left ⟶ L.sheaf))
        (hs : ∀ y : A.abelian.scheme.left, ∃ i, y ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)),
        IsClosedImmersion (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom s hs).left :=
  AmpleSectionEmbedding.PolarizationEmbedding.exists_closed_section_embedding _ _ (polarizationLine_isAmple_affine A)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.PolarizationEmbedding
