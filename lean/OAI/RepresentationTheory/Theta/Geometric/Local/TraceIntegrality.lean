import OAI.RepresentationTheory.Theta.Geometric.Local.TraceCoordinates
import OAI.RepresentationTheory.Theta.Geometric.Local.MatrixLattice

/-! # Trace Integrality -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The original integral polarization remains integral on the full
completed lattice. Its explicit split coefficients are integral. -/

open scoped Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.localTracePairing_integral (hg : D.pel.HasIntegralModelGeometry) (hc : D.HasFiniteCoordinates)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)
    (x y : Fin s × Bool → Fin 3 → ℚ_[q]) (hx : x ∈ D.jointLocalLattice) (hy : y ∈ D.jointLocalLattice) :
    D.localTracePairing x y ∈ Set.range (algebraMap ℤ_[q] ℚ_[q]) := by
  let B := D.localTracePairing.restrictScalars₁₂ ℤ_[q] ℤ_[q]
  let J : Submodule ℤ_[q] ℚ_[q] := (Algebra.linearMap ℤ_[q] ℚ_[q]).range
  change B x y ∈ J
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have htrace : ∀ a b : D.pel.reference.lattice,
        (D.pel.reference.integralForm a b : ℚ) = D.pel.reference.traceForm a b := by
      rcases hg.reference_admissible with ⟨_, _, _, _, _, _, _, _, _, _, h, _⟩
      exact h
    refine ⟨(D.pel.reference.integralForm ⟨a, ha⟩ ⟨b, hb⟩ : ℤ_[q]), ?_⟩
    change algebraMap ℤ_[q] ℚ_[q] (D.pel.reference.integralForm ⟨a, ha⟩ ⟨b, hb⟩ : ℤ_[q]) =
      D.localTracePairing (D.jointLocalEmbedding a) (D.jointLocalEmbedding b)
    rw [D.localTracePairing_reference hc hgood hdegree, ← htrace ⟨a, ha⟩ ⟨b, hb⟩]
    simp
  | zero_left y _ =>
    rw [map_zero, LinearMap.zero_apply]
    exact J.zero_mem
  | zero_right x _ =>
    rw [map_zero]
    exact J.zero_mem
  | add_left x y z _ _ _ hx hy =>
    rw [map_add, LinearMap.add_apply]
    exact J.add_mem hx hy
  | add_right x y z _ _ _ hy hz =>
    rw [map_add]
    exact J.add_mem hy hz
  | smul_left c x y _ _ h =>
    rw [LinearMap.map_smul₂]
    exact J.smul_mem c h
  | smul_right c x y _ _ h =>
    rw [map_smul]
    exact J.smul_mem c h

theorem Data.ActiveHeckeThetaData.jointLocalLattice_unit (hg : D.pel.HasIntegralModelGeometry) (hc : D.HasFiniteCoordinates)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (v : Fin s × Bool) (i : Fin 3) :
    Pi.single v (Pi.single i (1 : ℚ_[q])) ∈ D.jointLocalLattice := by
  apply D.jointLocalLattice_single hg hc hgood
  rw [hc.2.1]
  exact Submodule.subset_span ⟨i, rfl⟩

theorem Data.ActiveHeckeThetaData.localTracePairing_unit_left (v : Fin s × Bool) (i : Fin 3)
    (y : Fin s × Bool → Fin 3 → ℚ_[q]) :
    D.localTracePairing (Pi.single v (Pi.single i 1)) y =
      D.localTraceCoefficient v i * y (v.1, !v.2) i := by
  simp [D.localTracePairing_apply, Pi.single_apply, ite_apply]

theorem Data.ActiveHeckeThetaData.localTraceCoefficient_integral (hg : D.pel.HasIntegralModelGeometry) (hc : D.HasFiniteCoordinates)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)
    (v : Fin s × Bool) (i : Fin 3) : ‖D.localTraceCoefficient v i‖ ≤ 1 := by
  have h := D.localTracePairing_integral hg hc hgood hdegree _ _
    (D.jointLocalLattice_unit hg hc hgood v i) (D.jointLocalLattice_unit hg hc hgood (v.1, !v.2) i)
  rw [D.localTracePairing_unit_left, Pi.single_eq_same, Pi.single_eq_same, mul_one] at h
  obtain ⟨a, ha⟩ := h
  have he : (a : ℚ_[q]) = D.localTraceCoefficient v i := ha
  rw [← he]
  exact a.property

end

end OAI.RepresentationTheory.Theta.Geometric
