import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.QuotientBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.QuotientKernel
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.EqualityGluing
import OAI.AlgebraicGeometry.Resolution.Blowups.GeneratedBlowupCover

/-! # Ideal Chart Descent -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.IdealChartDescent.Construction

noncomputable section

/-! Actual isomorphic blowup charts detect original affine ideal containments. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem affineQuotientKernel_comap_hom {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (φ : R →+* S) :
    (QuotientKernel.Construction.affineQuotientKernel I).comap (Spec.map (CommRingCat.ofHom φ)) =
      QuotientKernel.Construction.affineQuotientKernel (I.map φ) := by
  let : Algebra R S := φ.toAlgebra
  exact QuotientBaseChange.Construction.affineQuotient_kernel_comap (S := S) I

theorem affineQuotientKernel_le_iff {R : Type u} [CommRing R] (I J : Ideal R) :
    QuotientKernel.Construction.affineQuotientKernel I ≤ QuotientKernel.Construction.affineQuotientKernel J ↔ I ≤ J := by
  constructor
  · intro h
    have htop := h ⟨⊤, isAffineOpen_top (Spec (.of R))⟩
    rw [QuotientKernel.Construction.affineQuotientKernel_idealTop, QuotientKernel.Construction.affineQuotientKernel_idealTop] at htop
    exact (Ideal.comap_le_comap_iff_of_surjective (Scheme.ΓSpecIso (.of R)).hom.hom
      (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.surjective I J).mp htop
  · intro h
    apply Scheme.IdealSheafData.le_of_isAffine
    rw [QuotientKernel.Construction.affineQuotientKernel_idealTop, QuotientKernel.Construction.affineQuotientKernel_idealTop]
    exact Ideal.comap_mono h

theorem idealSheaf_comap_le_iff_isIso {X Y : Scheme.{u}} (I J : Y.IdealSheafData)
    (g : X ⟶ Y) [IsIso g] : I.comap g ≤ J.comap g ↔ I ≤ J := by
  constructor
  · intro h
    have h' := Scheme.IdealSheafData.comap_mono (inv g) h
    change (I.comap g).comap (inv g) ≤ (J.comap g).comap (inv g) at h'
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      IsIso.inv_hom_id, Scheme.IdealSheafData.comap_id, Scheme.IdealSheafData.comap_id] at h'
    exact h'
  · intro h
    exact Scheme.IdealSheafData.comap_mono g h

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Original ideal containments can be checked on every actual denominator
chart of an isomorphic blowup, without choosing a localization presentation. -/
theorem ideal_le_of_isIso_blowup_chart_maps (I J K : Ideal R)
    [IsIso (ReesGrading.Construction.affineBlowupToSpec I)]
    (h : ∀ a : I, J.map (Blowup.Charts.Construction.blowupChartConstants I a) ≤ K.map (Blowup.Charts.Construction.blowupChartConstants I a)) : J ≤ K := by
  let π := ReesGrading.Construction.affineBlowupToSpec I
  let : IsLocallyNoetherian (ReesGrading.Construction.affineBlowup I) := LocallyOfFiniteType.isLocallyNoetherian π
  apply (affineQuotientKernel_le_iff J K).mp
  apply (idealSheaf_comap_le_iff_isIso _ _ π).mp
  have hchart (a : I) :
      ((QuotientKernel.Construction.affineQuotientKernel J).comap π).comap
        (Proj.awayι (ReesGrading.Construction.reesGrade I) (Blowup.Charts.Construction.reesGenerator I a) (Blowup.Charts.Construction.reesGenerator_mem I a) (by decide)) ≤
      ((QuotientKernel.Construction.affineQuotientKernel K).comap π).comap
        (Proj.awayι (ReesGrading.Construction.reesGrade I) (Blowup.Charts.Construction.reesGenerator I a) (Blowup.Charts.Construction.reesGenerator_mem I a) (by decide)) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
    change (QuotientKernel.Construction.affineQuotientKernel J).comap (_ ≫ ReesGrading.Construction.affineBlowupToSpec I) ≤
      (QuotientKernel.Construction.affineQuotientKernel K).comap (_ ≫ ReesGrading.Construction.affineBlowupToSpec I)
    rw [Blowup.Charts.Construction.affineBlowup_chart_structureMap, affineQuotientKernel_comap_hom,
      affineQuotientKernel_comap_hom]
    exact (affineQuotientKernel_le_iff _ _).mpr (h a)
  exact IdealSheaf.EqualityGluing.Construction.idealSheaf_le_of_openCover _ _ (Blowup.Cover.Construction.affineBlowupAffineCover I).openCover hchart

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.IdealChartDescent.Construction
