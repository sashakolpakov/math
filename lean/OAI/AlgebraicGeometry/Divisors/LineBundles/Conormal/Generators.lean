import Mathlib.RingTheory.Ideal.Cotangent

/-! # Generators -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.Generators.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual ideal generators lifted from conormal generators -/

variable {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R)

theorem idealCotangent_map_eq_top (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    (M : Submodule R I) (hM : M.map I.toCotangent = ⊤) : M = ⊤ := by
  apply eq_top_iff.mpr
  apply (Submodule.map_le_map_iff_of_injective (Submodule.injective_subtype _) _ _).mp
  rw [Submodule.map_top, Submodule.range_subtype]
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _) hI
  rw [smul_eq_mul, ← pow_two, ← Ideal.map_toCotangent_ker, ← Submodule.map_sup,
    ← Submodule.comap_map_eq, hM, Submodule.comap_top, Submodule.map_top, Submodule.range_subtype]

theorem idealCotangent_lifts_generate (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    {ι : Type*} (v : ι → I)
    (hv : Submodule.span R (Set.range (fun i => I.toCotangent (v i))) = ⊤) :
    Ideal.span (Set.range (fun i => (v i : R))) = I := by
  have hm : (Submodule.span R (Set.range v)).map I.toCotangent = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact hv
  have htop := idealCotangent_map_eq_top I hI (Submodule.span R (Set.range v)) hm
  have h := congrArg (Submodule.map I.subtype) htop
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype] at h
  exact h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.Generators.BundleCycles
