import OAI.AlgebraicGeometry.Resolution.Blowups.RefinedNormalDerivative
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RefinementHelpers

/-! # Refined Normal Open -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.RefinedNormalOpen.Construction

noncomputable section

/-! The actual refined normal neighborhood is open and retains its specified prime. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]

theorem refinedNormalOpen_isOpenImmersion (D : Derivation k A A) (z : A)
    (f : DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))) := by
  have he : CommRingCat.ofHom (algebraMap A (Localization.Away f)) =
      CommRingCat.ofHom (algebraMap A (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z)) ≫
        CommRingCat.ofHom (algebraMap (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) (Localization.Away f)) :=
    congrArg CommRingCat.ofHom (IsScalarTower.algebraMap_eq A (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) _)
  rw [he, Spec.map_comp]
  infer_instance

theorem refinedNormalOpen_lifts_prime (D : Derivation k A A) (z : A)
    (f : DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) (q : PrimeSpectrum A)
    (η : Localization.Away f →+* q.asIdeal.ResidueField)
    (hη : ∀ a : A, η (algebraMap A (Localization.Away f) a) = algebraMap A q.asIdeal.ResidueField a) :
    ∃ Q : PrimeSpectrum (Localization.Away f),
      PrimeSpectrum.comap (algebraMap A (Localization.Away f)) Q = q := by
  refine ⟨⟨RingHom.ker η, RingHom.ker_isPrime η⟩, ?_⟩
  apply PrimeSpectrum.ext
  ext a
  change η (algebraMap A (Localization.Away f) a) = 0 ↔ a ∈ q.asIdeal
  rw [hη, Ideal.algebraMap_residueField_eq_zero]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.RefinedNormalOpen.Construction
