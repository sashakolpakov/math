import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.FlatIdealDescent
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.FactorUniqueness
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-! # Factor Naturality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.FactorNaturality.Construction

noncomputable section

/-! Primitive boundary factorizations transfer exactly through pointed flat comparisons. -/

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The actual map between corresponding local rings of a flat morphism
is faithfully flat. -/
theorem pointed_flat_localRingHom_faithfullyFlat (f : R →+* S) (hf : f.Flat)
    (q : Ideal R) (Q : Ideal S) [q.IsPrime] [Q.IsPrime] (hQ : q = Q.comap f) :
    (Localization.localRingHom q Q f hQ).FaithfullyFlat := by
  let : Algebra R S := f.toAlgebra
  let : Module.Flat R S := hf
  let : Q.LiesOver q := ⟨hQ⟩
  let : Algebra (Localization.AtPrime q) (Localization.AtPrime Q) :=
    Localization.AtPrime.algebraOfLiesOver q Q
  let : IsLocalHom (algebraMap (Localization.AtPrime q) (Localization.AtPrime Q)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRingHom q Q f hQ
  let : Module.FaithfullyFlat (Localization.AtPrime q) (Localization.AtPrime Q) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance

/-- Faithfully flat comparison maps reflect ideal inclusion. -/
theorem faithfullyFlat_map_ideal_le_iff (f : R →+* S) (hf : f.FaithfullyFlat) (I J : Ideal R) :
    I.map f ≤ J.map f ↔ I ≤ J := by
  let : Algebra R S := f.toAlgebra
  let : Module.FaithfullyFlat R S := hf
  change I.map (algebraMap R S) ≤ J.map (algebraMap R S) ↔ I ≤ J
  constructor
  · intro h
    have hc : (I.map (algebraMap R S)).comap (algebraMap R S) ≤
        (J.map (algebraMap R S)).comap (algebraMap R S) := Ideal.comap_mono h
    rwa [Ideal.comap_map_eq_self_of_faithfullyFlat, Ideal.comap_map_eq_self_of_faithfullyFlat] at hc
  · exact Ideal.map_mono

/-- Every boundary-divisibility threshold, and hence the exact boundary
exponent, is preserved by a faithfully flat comparison map. -/
theorem faithfullyFlat_boundary_power_iff (f : R →+* S) (hf : f.FaithfullyFlat)
    (J : Ideal R) (z : R) (n : ℕ) :
    J.map f ≤ Ideal.span {f z} ^ n ↔ J ≤ Ideal.span {z} ^ n := by
  have h := faithfullyFlat_map_ideal_le_iff f hf J (Ideal.span {z} ^ n)
  simpa only [Ideal.map_pow, Ideal.map_span, Set.image_singleton] using h

variable {ι : Type*}

/-- A primitive factorization stays primitive on the comparison chart,
with exactly the same exponents and the actual extended residual ideal. -/
theorem faithfullyFlat_boundary_factorization_map (f : R →+* S) (hf : f.FaithfullyFlat)
    (B : Finset ι) (z : ι → R) (a : ι → ℕ) (J L : Ideal R)
    (hfactor : J = Ideal.span {∏ i ∈ B, z i ^ a i} * L)
    (hL : ∀ i ∈ B, ¬ L ≤ Ideal.span {z i}) :
    J.map f = Ideal.span {∏ i ∈ B, f (z i) ^ a i} * L.map f ∧
      ∀ i ∈ B, ¬ L.map f ≤ Ideal.span {f (z i)} := by
  refine ⟨?_, ?_⟩
  · simpa only [Ideal.map_mul, Ideal.map_span, Set.image_singleton, map_prod, map_pow]
      using congrArg (Ideal.map f) hfactor
  · intro i hi h
    apply hL i hi
    apply (faithfullyFlat_map_ideal_le_iff f hf L (Ideal.span {z i})).mp
    simpa only [Ideal.map_span, Set.image_singleton] using h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.FactorNaturality.Construction
