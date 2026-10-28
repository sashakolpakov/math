import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ScalarExtension
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.IntegerQuotient
import Mathlib.RingTheory.MvPolynomial.Basic

/-! # Coefficient Quotient Retraction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientQuotientRetraction.GradedHilbert

noncomputable section

/-! Coefficient extension of homogeneous quotient rings has a polynomial-linear retraction whenever a coefficient functional sends one to one. -/

open _root_.MvPolynomial

universe u v

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L] {n : ℕ}

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n))

def coefficientQuotientExtension :
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal) →ₗ[Hilbert.Polynomial.GradedHilbert.CoordinateRing K n]
      Hilbert.Polynomial.GradedHilbert.CoordinateRing L n ⧸ (ScalarExtension.GradedHilbert.scalarExtendedHomogeneousIdeal (L := L) I).toIdeal where
  toFun := Ideal.quotientMap (CoefficientMaps.GradedHilbert.scalarExtendedIdeal (L := L) I.toIdeal)
    (MvPolynomial.map (algebraMap K L)) (Ideal.le_comap_map)
  map_add' := map_add _
  map_smul' a x := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap K L) (a * p)) =
      Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap K L) a * MvPolynomial.map (algebraMap K L) p)
    rw [map_mul]

theorem coefficientQuotientExtension_mk (p : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) :
    coefficientQuotientExtension (L := L) I (Ideal.Quotient.mk I.toIdeal p) =
      Ideal.Quotient.mk (CoefficientMaps.GradedHilbert.scalarExtendedIdeal (L := L) I.toIdeal) (MvPolynomial.map (algebraMap K L) p) := rfl

def coefficientQuotientRetraction (φ : L →ₗ[K] K) :
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing L n ⧸ (ScalarExtension.GradedHilbert.scalarExtendedHomogeneousIdeal (L := L) I).toIdeal) →ₗ[Hilbert.Polynomial.GradedHilbert.CoordinateRing K n]
      Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal where
  toFun := Quotient.lift (fun f => Ideal.Quotient.mk I.toIdeal (CoefficientMaps.GradedHilbert.coefficientApply φ f)) (by
    intro f g h
    apply Ideal.Quotient.eq.mpr
    rw [← map_sub]
    exact CoefficientMaps.GradedHilbert.coefficientApply_mem_of_mem_scalarExtendedIdeal I.toIdeal φ ((Submodule.quotientRel_def _).mp h))
  map_add' x y := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk I.toIdeal (CoefficientMaps.GradedHilbert.coefficientApply φ (f + g)) = _
    rw [map_add, map_add]
    rfl
  map_smul' a x := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk I.toIdeal (CoefficientMaps.GradedHilbert.coefficientApply φ (MvPolynomial.map (algebraMap K L) a * p)) =
      Ideal.Quotient.mk I.toIdeal (a * CoefficientMaps.GradedHilbert.coefficientApply φ p)
    rw [CoefficientMaps.GradedHilbert.coefficientApply_map_mul]

theorem coefficientQuotientRetraction_mk (φ : L →ₗ[K] K) (p : Hilbert.Polynomial.GradedHilbert.CoordinateRing L n) :
    coefficientQuotientRetraction I φ (Ideal.Quotient.mk (CoefficientMaps.GradedHilbert.scalarExtendedIdeal (L := L) I.toIdeal) p) =
      Ideal.Quotient.mk I.toIdeal (CoefficientMaps.GradedHilbert.coefficientApply φ p) := rfl

theorem coefficientQuotientRetraction_extension (φ : L →ₗ[K] K) (hφ : φ 1 = 1)
    (x : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal) :
    coefficientQuotientRetraction I φ (coefficientQuotientExtension (L := L) I x) = x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [coefficientQuotientExtension_mk, coefficientQuotientRetraction_mk,
    CoefficientMaps.GradedHilbert.coefficientApply_map, hφ, one_smul]

theorem coefficientQuotientExtension_homogeneous (d : ℤ) (x : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal)
    (hx : x ∈ Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I d) :
    coefficientQuotientExtension (L := L) I x ∈
      Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (ScalarExtension.GradedHilbert.scalarExtendedHomogeneousIdeal (L := L) I) d := by
  obtain ⟨p, hp, rfl⟩ := hx
  refine ⟨MvPolynomial.map (algebraMap K L) p, ?_, rfl⟩
  intro m hm
  apply hp
  intro hz
  exact hm (by rw [MvPolynomial.coeff_map, hz, map_zero])

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientQuotientRetraction.GradedHilbert
