import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! # Faithful Local Completion -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.FaithfulLocalCompletion.Analytic

noncomputable section

/-! Completion along an ideal inside the maximal ideal of a Noetherian
local ring is faithfully flat. -/

theorem local_completion_faithfullyFlat (R : Type*) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) :
    Module.FaithfullyFlat R (AdicCompletion I R) := by
  let m := IsLocalRing.maximalIdeal R
  let φ : AdicCompletion I R →+* R ⧸ m :=
    (Ideal.Quotient.factor hI).comp (AdicCompletion.evalOneₐ I).toRingHom
  have hker : m.map (algebraMap R (AdicCompletion I R)) ≤ RingHom.ker φ := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change φ (algebraMap R (AdicCompletion I R) r) = 0
    change Ideal.Quotient.mk m r = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
  refine ⟨fun J hJ => ?_⟩
  rw [IsLocalRing.eq_maximalIdeal hJ, Ideal.smul_top_eq_map]
  intro htop
  have hmem : (1 : AdicCompletion I R) ∈ m.map (algebraMap R (AdicCompletion I R)) := by
    have h : (1 : AdicCompletion I R) ∈ (⊤ : Submodule R (AdicCompletion I R)) := Submodule.mem_top
    rw [← htop] at h
    exact h
  have hz : φ 1 = 0 := hker hmem
  exact one_ne_zero (by simpa only [map_one] using hz)

end

end OAI.AlgebraicGeometry.Comparison.Betti.FaithfulLocalCompletion.Analytic
