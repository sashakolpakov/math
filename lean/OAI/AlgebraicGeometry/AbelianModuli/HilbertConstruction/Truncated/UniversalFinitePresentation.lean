import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.UniversalFamilyCharts

/-! # Universal Finite Presentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.UniversalFinitePresentation

noncomputable section

/-! The actual global generated family is locally of finite presentation over its parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (S : Scheme.{u}) (n B : ℕ) (r : ℕ → ℕ)

theorem truncatedUniversalFamily_locallyFinitePresentation :
    LocallyOfFinitePresentation (UniversalIdeal.truncatedUniversalFamily S n B r).hom := by
  let : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFinitePresentation.{u})
      (Q := RingHom.FinitePresentation)
  let M := GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S
  let C := M.left.affineOpenCover
  apply IsZariskiLocalAtTarget.of_openCover (P := @LocallyOfFinitePresentation) C.openCover
  intro i
  let x := C.f i
  let h := UniversalFamilyCharts.truncatedUniversalFamilyChart_isPullback x
  have hh : LocallyOfFinitePresentation
      (h.isoPullback.inv ≫ (AffineUniversalData.truncatedAffineUniversalData x).projectiveFamily.hom) := inferInstance
  have he : h.isoPullback.inv ≫ (AffineUniversalData.truncatedAffineUniversalData x).projectiveFamily.hom =
      C.openCover.pullbackHom (UniversalIdeal.truncatedUniversalFamily S n B r).hom i := h.isoPullback_inv_snd
  exact he ▸ hh

theorem truncatedUniversalFamily_flat_of_affine_degree_flat
    (hflat : ∀ i : (GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S).left.affineOpenCover.I₀,
      ∃ N : ℕ, ∀ d ≥ N, Module.Flat
        ((GradedParameters.truncatedGradedParameters (Fin (n + 1)) B r S).left.affineOpenCover.X i)
        (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient
          (AffineUniversalData.truncatedAffineUniversalData
            ((GradedParameters.truncatedGradedParameters (Fin (n + 1)) B r S).left.affineOpenCover.f i)).generatedIdeal.toIdeal d)) :
    Flat (UniversalIdeal.truncatedUniversalFamily S n B r).hom := by
  let : IsZariskiLocalAtTarget (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{u}) (Q := RingHom.Flat)
  let M := GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S
  let C := M.left.affineOpenCover
  apply IsZariskiLocalAtTarget.of_openCover (P := @Flat) C.openCover
  intro i
  let x := C.f i
  let h := UniversalFamilyCharts.truncatedUniversalFamilyChart_isPullback x
  obtain ⟨N, hN⟩ := hflat i
  have : Flat (AffineUniversalData.truncatedAffineUniversalData x).projectiveFamily.hom :=
    (AffineUniversalData.truncatedAffineUniversalData x).projectiveFamily_flat N hN
  have hh : Flat (h.isoPullback.inv ≫ (AffineUniversalData.truncatedAffineUniversalData x).projectiveFamily.hom) := inferInstance
  have he : h.isoPullback.inv ≫ (AffineUniversalData.truncatedAffineUniversalData x).projectiveFamily.hom =
      C.openCover.pullbackHom (UniversalIdeal.truncatedUniversalFamily S n B r).hom i := h.isoPullback_inv_snd
  exact he ▸ hh

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.UniversalFinitePresentation
