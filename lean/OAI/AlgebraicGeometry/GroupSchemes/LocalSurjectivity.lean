import Mathlib

/-! # Local Surjectivity -/

namespace OAI.AlgebraicGeometry.GroupSchemes.LocalSurjectivity.FiniteEtale

noncomputable section

/-! Two applications of Nakayama for finite maps of local rings. -/

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

/-- A finite local map surjective on residues and on the maximal ideal is surjective. -/
theorem surjective_of_map_maximalIdeal (f : R →+* S) (hf : f.Finite)
    (hm : (IsLocalRing.maximalIdeal R).map f = IsLocalRing.maximalIdeal S)
    (hres : ∀ y : S, ∃ x : R, y - f x ∈ IsLocalRing.maximalIdeal S) :
    Function.Surjective f := by
  algebraize [f]
  have : Module.Finite R S := hf
  change (IsLocalRing.maximalIdeal R).map (algebraMap R S) = IsLocalRing.maximalIdeal S at hm
  change Function.Surjective (Algebra.linearMap R S)
  rw [← LinearMap.range_eq_top, ← top_le_iff]
  apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
  rw [Ideal.smul_top_eq_map, hm]
  intro y _
  obtain ⟨x, hx⟩ := hres y
  exact Submodule.mem_sup.mpr ⟨f x, ⟨x, rfl⟩, y - f x, hx, by abel⟩

/-- Surjectivity on cotangent spaces already gives surjectivity on the maximal ideal. -/
theorem map_maximalIdeal_of_cotangent [IsNoetherianRing S] (f : R →+* S)
    (hle : (IsLocalRing.maximalIdeal R).map f ≤ IsLocalRing.maximalIdeal S)
    (hcot : IsLocalRing.maximalIdeal S ≤
      (IsLocalRing.maximalIdeal R).map f ⊔ IsLocalRing.maximalIdeal S ^ 2) :
    (IsLocalRing.maximalIdeal R).map f = IsLocalRing.maximalIdeal S := by
  apply le_antisymm hle
  apply Submodule.le_of_le_smul_of_le_jacobson_bot
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal S))
    (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal S))
  simpa only [Ideal.smul_eq_mul, pow_two] using hcot

/-- A finite local map surjective on residues and cotangent spaces is surjective. -/
theorem surjective_of_cotangent [IsNoetherianRing S] (f : R →+* S) (hf : f.Finite)
    (hle : (IsLocalRing.maximalIdeal R).map f ≤ IsLocalRing.maximalIdeal S)
    (hcot : IsLocalRing.maximalIdeal S ≤
      (IsLocalRing.maximalIdeal R).map f ⊔ IsLocalRing.maximalIdeal S ^ 2)
    (hres : ∀ y : S, ∃ x : R, y - f x ∈ IsLocalRing.maximalIdeal S) :
    Function.Surjective f :=
  surjective_of_map_maximalIdeal f hf (map_maximalIdeal_of_cotangent f hle hcot) hres

end

end OAI.AlgebraicGeometry.GroupSchemes.LocalSurjectivity.FiniteEtale
