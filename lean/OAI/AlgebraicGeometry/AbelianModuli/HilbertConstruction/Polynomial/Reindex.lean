import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Reindex -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.Reindex

noncomputable section

/-!
Reindexing the variables of a polynomial ring preserves its standard grading
and induces an isomorphism of projective schemes. The coefficient universe
contains both index universes, allowing later reindexing by a finite ordinal.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable (R : Type (max u v)) [CommRing R]
variable {σ : Type u} {τ : Type v}

attribute [local instance] MvPolynomial.gradedAlgebra

def polynomialReindexGraded (e : σ ≃ τ) :
    MvPolynomial.homogeneousSubmodule σ R →+*ᵍ
      MvPolynomial.homogeneousSubmodule τ R where
  __ := (MvPolynomial.renameEquiv R e).toRingEquiv.toRingHom
  map_mem h := h.rename_isHomogeneous

theorem polynomialReindexGraded_inverse (e : σ ≃ τ) :
    (polynomialReindexGraded R e.symm).comp (polynomialReindexGraded R e) =
      GradedRingHom.id (MvPolynomial.homogeneousSubmodule σ R) := by
  apply GradedRingHom.ext
  intro p
  exact (MvPolynomial.renameEquiv R e).symm_apply_apply p

theorem polynomialReindexGraded_irrelevant (e : σ ≃ τ) :
    HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule τ R) ≤
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule σ R)).map
        (polynomialReindexGraded R e) := by
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro d hd p hp
  have hpre := (polynomialReindexGraded R e.symm).map_mem hp
  have hmem := HomogeneousIdeal.mem_irrelevant_of_mem
    (MvPolynomial.homogeneousSubmodule σ R) hd hpre
  have himage := Ideal.mem_map_of_mem (polynomialReindexGraded R e).toRingHom hmem
  change (polynomialReindexGraded R e) ((polynomialReindexGraded R e.symm) p) ∈
    ((HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule σ R)).map
      (polynomialReindexGraded R e)).toIdeal at himage
  have hcancel : (polynomialReindexGraded R e)
      ((polynomialReindexGraded R e.symm) p) = p :=
    (MvPolynomial.renameEquiv R e).apply_symm_apply p
  rwa [hcancel] at himage

def polynomialProjectiveReindexIso (e : σ ≃ τ) :
    Proj (MvPolynomial.homogeneousSubmodule σ R) ≅
      Proj (MvPolynomial.homogeneousSubmodule τ R) where
  hom := Proj.map (polynomialReindexGraded R e.symm)
    (polynomialReindexGraded_irrelevant R e.symm)
  inv := Proj.map (polynomialReindexGraded R e)
    (polynomialReindexGraded_irrelevant R e)
  hom_inv_id := by
    rw [← Proj.map_comp]
    simp only [polynomialReindexGraded_inverse R e, Proj.map_id]
  inv_hom_id := by
    rw [← Proj.map_comp]
    have h := polynomialReindexGraded_inverse R e.symm
    simp only [Equiv.symm_symm] at h
    simp only [h, Proj.map_id]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.Reindex
