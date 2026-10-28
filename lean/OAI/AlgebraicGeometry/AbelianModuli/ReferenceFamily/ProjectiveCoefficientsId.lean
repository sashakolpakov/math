import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StandardProjectiveCharts
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-! # Projective Coefficients Id -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectiveCoefficientsId.ProjectiveCoefficients

noncomputable section

/-! Actual projective-space maps induced by changes of coefficient
ring. Ring isomorphisms give actual scheme isomorphisms, needed to
compare HilbertConstruction projective presentations with the native complex model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R T U : Type} [CommRing R] [CommRing T] [CommRing U]

def gradedMap (f : R →+* T) (n : ℕ) : HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n →+*ᵍ HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading T n where
  toRingHom := MvPolynomial.map f
  map_mem h := MvPolynomial.IsHomogeneous.map h f

theorem gradedMap_irrelevant (f : R →+* T) (n : ℕ) :
    HomogeneousIdeal.irrelevant (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading T n) ≤
      (HomogeneousIdeal.irrelevant (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n)).map (gradedMap f n) := by
  change (HomogeneousIdeal.irrelevant (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading T n)).toIdeal ≤
    ((HomogeneousIdeal.irrelevant (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n)).toIdeal).map (gradedMap f n).toRingHom
  apply (HilbertConstruction.StandardProjectiveCharts.coordinate_irrelevant_le_span T n).trans
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have hi : MvPolynomial.X i ∈ (HomogeneousIdeal.irrelevant (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n)).toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.zero_lt_one (MvPolynomial.isHomogeneous_X R i)
  have hm := Ideal.mem_map_of_mem (gradedMap f n).toRingHom hi
  have he : gradedMap f n (MvPolynomial.X i) = MvPolynomial.X i := MvPolynomial.map_X f i
  exact he ▸ hm

def schemeMap (f : R →+* T) (n : ℕ) :
    (HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace T n).left ⟶ (HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n).left :=
  Proj.map (gradedMap f n) (gradedMap_irrelevant f n)

theorem gradedMap_comp (f : R →+* T) (h : T →+* U) (n : ℕ) :
    gradedMap (h.comp f) n = (gradedMap h n).comp (gradedMap f n) := by
  apply GradedRingHom.ext
  intro p
  exact (MvPolynomial.map_map f h p).symm

theorem gradedMap_id (n : ℕ) : gradedMap (RingHom.id R) n = GradedRingHom.id (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) := by
  apply GradedRingHom.ext
  intro p
  exact MvPolynomial.map_id p

theorem projMap_congr {n : ℕ}
    {f h : HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n →+*ᵍ HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading T n} (e : f = h)
    (hf : HomogeneousIdeal.irrelevant (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading T n) ≤
      (HomogeneousIdeal.irrelevant (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n)).map f)
    (hh : HomogeneousIdeal.irrelevant (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading T n) ≤
      (HomogeneousIdeal.irrelevant (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n)).map h) :
    Proj.map f hf = Proj.map h hh := by
  subst h
  rfl

theorem schemeMap_comp (f : R →+* T) (h : T →+* U) (n : ℕ) :
    schemeMap (h.comp f) n = schemeMap h n ≫ schemeMap f n :=
  (projMap_congr (gradedMap_comp f h n) (gradedMap_irrelevant (h.comp f) n)
    (HomogeneousIdeal.irrelevant_le_map_comp (gradedMap_irrelevant f n) (gradedMap_irrelevant h n))).trans
      (Proj.map_comp _ _ _ _)

theorem schemeMap_id (n : ℕ) : schemeMap (RingHom.id R) n = 𝟙 _ :=
  (projMap_congr (gradedMap_id (R := R) n) (gradedMap_irrelevant (RingHom.id R) n)
    (by simp)).trans Proj.map_id

/-- Changing the coefficient ring by an isomorphism changes projective
space by an actual scheme isomorphism. -/
def schemeIso (e : R ≃+* T) (n : ℕ) :
    (HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace T n).left ≅ (HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n).left where
  hom := schemeMap e.toRingHom n
  inv := schemeMap e.symm.toRingHom n
  hom_inv_id := by
    rw [← schemeMap_comp]
    have h : e.toRingHom.comp e.symm.toRingHom = RingHom.id T := by ext x; exact e.apply_symm_apply x
    rw [h, schemeMap_id]
  inv_hom_id := by
    rw [← schemeMap_comp]
    have h : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := by ext x; exact e.symm_apply_apply x
    rw [h, schemeMap_id]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectiveCoefficientsId.ProjectiveCoefficients
