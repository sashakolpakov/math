import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicBoundary
import OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicEtaleMap
import OAI.AlgebraicGeometry.Resolution.Blowups.ActiveBoundaryNeighborhood

/-! # Logarithmic -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Relative.Logarithmic.Construction

noncomputable section

/-! Relative logarithmic bounds retain the geometric boundary consequences. -/

variable (k : Type*) {R ι : Type*} [CommRing k] [CommRing R] [Algebra k R]

theorem firstRelativeLogarithmicDifferentialIdeal_le_logarithmic (w : ι → R) (J : Ideal R) :
    LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k w J ≤ LogarithmicBoundaryReindex.Construction.firstLogarithmicDifferentialIdeal w J := by
  apply sup_le
  · exact LogarithmicBoundaryReindex.Construction.le_firstLogarithmicDifferentialIdeal w J
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨D, p⟩, rfl⟩
    exact LogarithmicBoundaryReindex.Construction.logarithmic_derivation_mem_first w J
      ⟨D.val.restrictScalars ℤ, fun i => D.property i⟩ p.property

theorem iteratedRelativeLogarithmicDifferentialIdeal_le_logarithmic
    (w : ι → R) (J : Ideal R) (n : ℕ) :
    LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J n ≤
      LogarithmicBoundaryReindex.Construction.iteratedLogarithmicDifferentialIdeal w J n := by
  induction n generalizing J with
  | zero => exact le_rfl
  | succ n ih =>
    exact (ih (LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k w J)).trans
      (LogarithmicBoundaryReindex.Construction.iteratedLogarithmicDifferentialIdeal_mono w n
        (firstRelativeLogarithmicDifferentialIdeal_le_logarithmic k w J))

theorem relative_logarithmic_bound_implies_logarithmic (w : ι → R) (J : Ideal R) (n : ℕ)
    (h : LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J n = ⊤) :
    LogarithmicBoundaryReindex.Construction.iteratedLogarithmicDifferentialIdeal w J n = ⊤ := by
  have hle := iteratedRelativeLogarithmicDifferentialIdeal_le_logarithmic k w J n
  rw [h] at hle
  exact top_le_iff.mp hle

theorem relative_logarithmic_bound_excludes_local_boundary_factor
    (w : ι → R) (J : Ideal R) (n : ℕ)
    (h : LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J n = ⊤)
    (q : Ideal R) [q.IsPrime] (i : ι) (hi : w i ∈ q) :
    ¬ J.map (algebraMap R (Localization.AtPrime q)) ≤
      Ideal.span {algebraMap R (Localization.AtPrime q) (w i)} :=
  LogarithmicEtaleMap.Construction.logarithmic_order_bound_excludes_local_boundary_factor w J n
    (relative_logarithmic_bound_implies_logarithmic k w J n h) q i hi

/-- Removing the boundary components absent from a point is carried out on
an actual principal open, preserving the stronger relative logarithmic bound. -/
theorem exists_relative_active_boundary_neighborhood
    {σ : Type*} [DecidableEq σ] (w : σ → R) (B : Finset σ)
    (J q : Ideal R) [q.IsPrime] (n : ℕ)
    (h : LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k (fun i : B => w i.val) J n = ⊤) :
    ∃ (C : Finset σ) (f : R), C ⊆ B ∧ f ∉ q ∧
      (∀ i ∈ B, i ∈ C ↔ w i ∈ q) ∧
      (∀ i ∈ B, i ∉ C → IsUnit (algebraMap R (Localization.Away f) (w i))) ∧
      LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k
        (fun i : C => algebraMap R (Localization.Away f) (w i.val))
        (J.map (algebraMap R (Localization.Away f))) n = ⊤ := by
  obtain ⟨C, f, hCB, hf, hC, hunit, _⟩ := ActiveBoundaryNeighborhood.Construction.exists_active_boundary_neighborhood w B J q n
    (relative_logarithmic_bound_implies_logarithmic k (fun i : B => w i.val) J n h)
  refine ⟨C, f, hCB, hf, hC, hunit, ?_⟩
  let : Algebra.FormallyEtale R (Localization.Away f) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers f)
  have hmap := LogarithmicBoundary.Construction.relative_logarithmic_order_bound_map (S := Localization.Away f) k
    (fun i : B => w i.val) J n h
  have hderiv := LogarithmicBoundary.Construction.relativeLogarithmicDerivations_remove_unit_components k
    (fun i => algebraMap R (Localization.Away f) (w i)) B C hCB hunit
  rw [LogarithmicBoundary.Construction.iteratedRelativeLogarithmicDifferentialIdeal_congr_derivations k _ _ hderiv] at hmap
  exact hmap

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Relative.Logarithmic.Construction
