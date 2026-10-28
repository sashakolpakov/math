import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Polynomial
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

/-! # Quotient -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.Quotient.GradedHilbert

noncomputable section

/-!
The grading on the actual quotient of a homogeneous coordinate ring.
This construction works over any commutative base ring and supplies the
graded quotient ring needed for projective-spectrum constructions.
-/

open _root_.MvPolynomial DirectSum

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

def quotientCoordinateMap (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    Hilbert.Polynomial.GradedHilbert.CoordinateRing R n →ₗ[R] Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal :=
  (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap

def quotientGrading (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ) :
    Submodule R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) :=
  (Hilbert.Polynomial.GradedHilbert.grading R n d).map (quotientCoordinateMap I)

def quotientDegreeMap (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ) :
    Hilbert.Polynomial.GradedHilbert.grading R n d →ₗ[R] quotientGrading I d :=
  ((quotientCoordinateMap I).comp (Hilbert.Polynomial.GradedHilbert.grading R n d).subtype).codRestrict
    (quotientGrading I d) (fun f => ⟨f.val, f.property, rfl⟩)

def quotientPreDecompose (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    Hilbert.Polynomial.GradedHilbert.CoordinateRing R n →ₗ[R] ⨁ d : ℕ, quotientGrading I d :=
  DirectSum.lmap (quotientDegreeMap I) ∘ₗ (DirectSum.decomposeLinearEquiv (Hilbert.Polynomial.GradedHilbert.grading R n)).toLinearMap

theorem quotientPreDecompose_mem_kernel (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    I.toIdeal.restrictScalars R ≤ LinearMap.ker (quotientPreDecompose I) := by
  intro f hf
  apply DFinsupp.ext
  intro d
  apply Subtype.ext
  change Ideal.Quotient.mk I.toIdeal ((DirectSum.decompose (Hilbert.Polynomial.GradedHilbert.grading R n) f d).val) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact (Ideal.IsHomogeneous.mem_iff (Hilbert.Polynomial.GradedHilbert.grading R n) I.isHomogeneous).mp hf d

def quotientDecompose (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) →ₗ[R] ⨁ d : ℕ, quotientGrading I d where
  toFun := Quotient.lift (quotientPreDecompose I) (by
    intro f g h
    have hfg : f - g ∈ I.toIdeal := (Submodule.quotientRel_def _).mp h
    have hz : quotientPreDecompose I (f - g) = 0 := quotientPreDecompose_mem_kernel I hfg
    rw [map_sub] at hz
    exact sub_eq_zero.mp hz)
  map_add' x y := Quotient.inductionOn₂ x y (fun f g => map_add (quotientPreDecompose I) f g)
  map_smul' r x := Quotient.inductionOn x (fun f => map_smul (quotientPreDecompose I) r f)

theorem quotientDecompose_mk (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :
    quotientDecompose I (Ideal.Quotient.mk I.toIdeal f) = quotientPreDecompose I f := rfl

theorem quotientDecompose_mk_homogeneous (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (d : ℕ) (f : Hilbert.Polynomial.GradedHilbert.grading R n d) :
    quotientDecompose I (quotientCoordinateMap I f.val) =
      DirectSum.lof R ℕ (fun d => quotientGrading I d) d (quotientDegreeMap I d f) := by
  rw [show quotientCoordinateMap I f.val = Ideal.Quotient.mk I.toIdeal f.val from rfl,
    quotientDecompose_mk]
  change DirectSum.lmap (quotientDegreeMap I) (DirectSum.decomposeLinearEquiv (Hilbert.Polynomial.GradedHilbert.grading R n) f.val) = _
  rw [DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.lmap_lof]

theorem quotientDecompose_left_inverse (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    DirectSum.coeLinearMap (quotientGrading I) ∘ₗ quotientDecompose I = LinearMap.id := by
  have h : (DirectSum.coeLinearMap (quotientGrading I) ∘ₗ quotientDecompose I) ∘ₗ
      quotientCoordinateMap I = quotientCoordinateMap I := by
    apply DirectSum.decompose_lhom_ext (Hilbert.Polynomial.GradedHilbert.grading R n)
    intro d
    apply LinearMap.ext
    intro f
    change DirectSum.coeLinearMap (quotientGrading I)
      (quotientDecompose I (quotientCoordinateMap I f.val)) = quotientCoordinateMap I f.val
    rw [quotientDecompose_mk_homogeneous, DirectSum.coeLinearMap_lof]
    rfl
  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun h f

theorem quotientDecompose_right_inverse (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    quotientDecompose I ∘ₗ DirectSum.coeLinearMap (quotientGrading I) = LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro d
  apply LinearMap.ext
  intro x
  obtain ⟨f, hf, hfx⟩ := x.property
  have hx : quotientDegreeMap I d ⟨f, hf⟩ = x := Subtype.ext hfx
  rw [← hx]
  change quotientDecompose I
    (DirectSum.coeLinearMap (quotientGrading I)
      (DirectSum.lof R ℕ (fun d => quotientGrading I d) d (quotientDegreeMap I d ⟨f, hf⟩))) = _
  rw [DirectSum.coeLinearMap_lof]
  exact quotientDecompose_mk_homogeneous I d ⟨f, hf⟩

instance quotientDecomposition (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    DirectSum.Decomposition (quotientGrading I) :=
  DirectSum.Decomposition.ofLinearMap (quotientGrading I) (quotientDecompose I)
    (quotientDecompose_left_inverse I) (quotientDecompose_right_inverse I)

instance quotientGradedAlgebra (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    GradedAlgebra (quotientGrading I) where
  one_mem := ⟨1, isHomogeneous_one _ _, map_one (Ideal.Quotient.mk I.toIdeal)⟩
  mul_mem d e x y hx hy := by
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨g, hg, rfl⟩ := hy
    exact ⟨f * g, hf.mul hg, map_mul (Ideal.Quotient.mk I.toIdeal) f g⟩

def gradedQuotientMap (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    Hilbert.Polynomial.GradedHilbert.grading R n →+*ᵍ quotientGrading I where
  __ := Ideal.Quotient.mk I.toIdeal
  map_mem hf := ⟨_, hf, rfl⟩

theorem quotientDegreeMap_surjective (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ) :
    Function.Surjective (quotientDegreeMap I d) := by
  intro x
  obtain ⟨f, hf, hfx⟩ := x.property
  exact ⟨⟨f, hf⟩, Subtype.ext hfx⟩

theorem quotientDegreeMap_kernel (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ) :
    LinearMap.ker (quotientDegreeMap I d) = Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d := by
  apply Submodule.ext
  intro f
  change quotientDegreeMap I d f = 0 ↔ f.val ∈ I.toIdeal
  rw [Subtype.ext_iff]
  exact Ideal.Quotient.eq_zero_iff_mem

def degreeQuotientEquivQuotientGrading (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ) :
    Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d ≃ₗ[R] quotientGrading I d :=
  (Submodule.quotEquivOfEq _ _ (quotientDegreeMap_kernel I d).symm).trans
    ((quotientDegreeMap I d).quotKerEquivOfSurjective (quotientDegreeMap_surjective I d))

theorem degreeQuotientEquivQuotientGrading_mk (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (d : ℕ) (f : Hilbert.Polynomial.GradedHilbert.grading R n d) :
    degreeQuotientEquivQuotientGrading I d ((Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).mkQ f) =
      quotientDegreeMap I d f := rfl

theorem irrelevant_quotient_le_map (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    HomogeneousIdeal.irrelevant (quotientGrading I) ≤
      (HomogeneousIdeal.irrelevant (Hilbert.Polynomial.GradedHilbert.grading R n)).map (gradedQuotientMap I) := by
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro d hd x hx
  obtain ⟨f, hf, rfl⟩ := hx
  exact Ideal.mem_map_of_mem (gradedQuotientMap I)
    (HomogeneousIdeal.mem_irrelevant_of_mem (Hilbert.Polynomial.GradedHilbert.grading R n) hd hf)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.Quotient.GradedHilbert
