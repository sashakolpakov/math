import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.PrimeLocalizationTower
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Refinement Point -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.RefinementPoint

noncomputable section

/-! Refining a principal neighborhood by an element inverted at the
chosen prime preserves a point over that prime. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]

theorem principalToPrime_spec_comp (s : A) (hs : s ∉ p) :
    Spec.map (CommRingCat.ofHom (PrimeLocalization.principalToPrimeMap p s hs)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s))) =
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime p))) := by
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (PrimeLocalizationTower.principalToPrimeMap_comp_algebraMap p s hs)

theorem principalRefinement_prime_factorization (s : A) (hs : s ∉ p)
    (t : p.primeCompl.map (algebraMap A (Localization.Away s))) :
    ∃ φ : Localization.Away t.val →+* Localization.AtPrime p,
      Spec.map (CommRingCat.ofHom φ) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away s) (Localization.Away t.val))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s)))) =
        Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime p))) := by
  let : Algebra (Localization.Away s) (Localization.AtPrime p) := (PrimeLocalization.principalToPrimeMap p s hs).toAlgebra
  let : IsLocalization (p.primeCompl.map (algebraMap A (Localization.Away s))) (Localization.AtPrime p) :=
    PrimeLocalizationTower.principalToPrime_isLocalization p s hs
  let φ : Localization.Away t.val →+* Localization.AtPrime p :=
    IsLocalization.Away.lift t.val (IsLocalization.map_units (Localization.AtPrime p) t)
  have hφ : φ.comp (algebraMap (Localization.Away s) (Localization.Away t.val)) =
      PrimeLocalization.principalToPrimeMap p s hs := IsLocalization.Away.lift_comp _ _
  refine ⟨φ, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (φ.comp (algebraMap (Localization.Away s) (Localization.Away t.val)))) ≫ _ = _
  rw [hφ]
  exact principalToPrime_spec_comp p s hs

theorem principalRefinement_contains_prime (p : PrimeSpectrum A) (s : A) (hs : s ∉ p.asIdeal)
    (t : p.asIdeal.primeCompl.map (algebraMap A (Localization.Away s))) :
    ∃ y : Spec (.of (Localization.Away t.val)),
      (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away s) (Localization.Away t.val))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s)))) y = p := by
  obtain ⟨φ, hφ⟩ := principalRefinement_prime_factorization p.asIdeal s hs t
  refine ⟨Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal)), ?_⟩
  have h := congrArg (fun f => f (IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal))) hφ
  exact h.trans (PrimeLocalizationTower.spec_primeLocalization_closedPoint p)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.RefinementPoint
