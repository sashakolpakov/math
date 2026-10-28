import OAI.AlgebraicGeometry.ComplexPoints.Analytic.PrincipalOpen
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Affine Point Spectrum -/

namespace OAI.AlgebraicGeometry

/-!
# Affine complex characters and their underlying spectrum points

An ordinary complex point of an affine algebra determines its prime kernel.
This map is continuous to the Zariski spectrum, and inverse images of scheme
basic opens are precisely the ordinary principal open subsets. The topology on
the source remains the evaluation topology on complex characters.
-/

universe u v

variable {A : Type u} [CommRing A] [Algebra ℂ A]

/-- The underlying prime-spectrum point of a complex algebra character. -/
def Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) : PrimeSpectrum A :=
  ⟨RingHom.ker x.toRingHom, RingHom.ker_isPrime x.toRingHom⟩

/-- A complex-algebra character is surjective, so its prime kernel is maximal. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum_isMaximal (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum x).asIdeal.IsMaximal := by
  change (RingHom.ker x.toRingHom).IsMaximal
  apply RingHom.ker_isMaximal_of_surjective x.toRingHom
  intro z
  refine ⟨algebraMap ℂ A z, ?_⟩
  simp

/-- The prime kernel is the usual spectrum image of the unique point of `Spec ℂ`. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum_eq_comap_bot (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum x = PrimeSpectrum.comap x.toRingHom
      (⟨⊥, by infer_instance⟩ : PrimeSpectrum ℂ) := rfl

/-- Scheme basic opens pull back to nonvanishing loci in the ordinary point topology. -/
@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum_preimage_basicOpen (a : A) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum ⁻¹' (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) =
      Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a := by
  ext x
  change (a ∉ RingHom.ker x.toRingHom) ↔ x.toRingHom a ≠ 0
  exact not_congr (RingHom.mem_ker (f := x.toRingHom) (r := a))

/-- Scheme closed loci pull back to the same equations on complex characters. -/
@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum_preimage_zeroLocus (S : Set A) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum ⁻¹' PrimeSpectrum.zeroLocus S =
      {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A | ∀ a ∈ S, x a = 0} := by
  ext x
  change (S ⊆ (RingHom.ker x.toRingHom : Set A)) ↔ ∀ a ∈ S, x a = 0
  constructor
  · intro hx a ha
    exact hx ha
  · intro hx a ha
    exact hx a ha

/-- The map from ordinary affine complex points to the Zariski spectrum is continuous. -/
@[continuity, fun_prop]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_toPrimeSpectrum :
    Continuous (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum (A := A)) := by
  rw [continuous_iff_isClosed]
  intro S hS
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus S).mp hS
  rw [Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum_preimage_zeroLocus]
  exact Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosed_commonZeroSet I

/-- Underlying spectrum points commute with pullback of complex characters. -/
@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum_comap {B : Type v} [CommRing B] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f x) = PrimeSpectrum.comap f.toRingHom (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum x) := by
  ext a
  rfl

end OAI.AlgebraicGeometry
