import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferentialCoefficientIdeal
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-! # Differential Ideal Point Support -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferentialIdealPointSupport

noncomputable section

/-! If the residue-field kernel of a differential vanishes away from one prime and its source has a basis vector, its coefficient-ideal quotient has at most one point. No reducedness is imposed on the quotient. -/
open _root_.Module
open scoped TensorProduct
universe u
variable {R M N : Type u} [CommRing R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]
variable {ι κ : Type u} (b : Basis ι R M) (c : Basis κ R N) (f : M →ₗ[R] N)

theorem differential_coefficients_not_le_of_residue_kernel_subsingleton
    (i : ι) (p : PrimeSpectrum R)
    (hp : Subsingleton (LinearMap.ker (f.baseChange p.asIdeal.ResidueField))) :
    ¬ DifferentialCoefficientIdeal.differentialCoefficientIdeal b c f ≤ p.asIdeal := by
  intro h
  have hz : f.baseChange p.asIdeal.ResidueField = 0 :=
    (DifferentialCoefficientIdeal.differential_baseChange_zero_iff_coefficients b c f p.asIdeal.ResidueField).mpr
      (by simpa only [Ideal.ker_algebraMap_residueField] using h)
  let z : LinearMap.ker (f.baseChange p.asIdeal.ResidueField) :=
    ⟨(b.baseChange p.asIdeal.ResidueField) i, by
      change (f.baseChange p.asIdeal.ResidueField) _ = 0
      rw [hz, LinearMap.zero_apply]⟩
  exact (b.baseChange p.asIdeal.ResidueField).ne_zero i
    (congrArg (fun x : LinearMap.ker (f.baseChange p.asIdeal.ResidueField) => x.val)
      (hp.elim z 0))

theorem differential_coefficient_quotient_subsingleton_of_residue_support
    (i : ι) (p₀ : PrimeSpectrum R)
    (h : ∀ p : PrimeSpectrum R, p ≠ p₀ →
      Subsingleton (LinearMap.ker (f.baseChange p.asIdeal.ResidueField))) :
    Subsingleton (PrimeSpectrum (R ⧸ DifferentialCoefficientIdeal.differentialCoefficientIdeal b c f)) := by
  let I := DifferentialCoefficientIdeal.differentialCoefficientIdeal b c f
  have hp (p : PrimeSpectrum R) (hI : I ≤ p.asIdeal) : p = p₀ := by
    by_contra hn
    exact differential_coefficients_not_le_of_residue_kernel_subsingleton b c f i p (h p hn) hI
  have hI (q : PrimeSpectrum (R ⧸ I)) :
      I ≤ (PrimeSpectrum.comap (Ideal.Quotient.mk I) q).asIdeal := by
    intro r hr
    change Ideal.Quotient.mk I r ∈ q.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
    exact q.asIdeal.zero_mem
  refine ⟨fun p q => ?_⟩
  apply PrimeSpectrum.comap_injective_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  exact (hp _ (hI p)).trans (hp _ (hI q)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferentialIdealPointSupport
