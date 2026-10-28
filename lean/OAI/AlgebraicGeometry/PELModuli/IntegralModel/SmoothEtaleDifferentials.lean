import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Smooth Etale Differentials -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothEtaleDifferentials

noncomputable section

/-! Differential criteria for descending smooth coordinates through an
etale source cover. Both the first cotangent homology and differentials
are the actual modules in the Jacobi--Zariski sequence. -/

open TensorProduct KaehlerDifferential

theorem formallyEtale_of_smooth_differential_comparison
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FormallySmooth R B]
    (h : Function.Bijective (KaehlerDifferential.mapBaseChange R A B)) :
    Algebra.FormallyEtale A B := by
  constructor
  · apply (subsingleton_iff_forall_eq 0).mpr
    intro x
    obtain ⟨y, rfl⟩ := KaehlerDifferential.map_surjective R A B x
    obtain ⟨z, rfl⟩ := h.2 y
    exact (KaehlerDifferential.exact_mapBaseChange_map R A B).apply_apply_eq_zero z
  · apply (subsingleton_iff_forall_eq 0).mpr
    intro x
    have hδ : Algebra.H1Cotangent.δ R A B x = 0 := by
      apply h.1
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R A B).apply_apply_eq_zero x
    obtain ⟨y, hy⟩ := (Algebra.H1Cotangent.exact_map_δ R A B x).mp hδ
    rw [← hy, Subsingleton.elim y 0, map_zero]

theorem differentials_flat_of_faithfully_flat_etale_cover
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Module.FaithfullyFlat A B] [Algebra.FormallyEtale A B]
    [Algebra.FormallySmooth R B] : Module.Flat A Ω[A⁄R] := by
  have : Module.Flat B (B ⊗[A] Ω[A⁄R]) :=
    Module.Flat.of_linearEquiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B)
  exact Module.Flat.of_flat_tensorProduct A Ω[A⁄R] B

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothEtaleDifferentials
