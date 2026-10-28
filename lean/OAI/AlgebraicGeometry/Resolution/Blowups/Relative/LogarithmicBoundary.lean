import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicEtaleMap

/-! # Logarithmic Boundary -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicBoundary.Construction

noncomputable section

section

/-! Reindexing, removing absent boundaries, and mapping relative logarithmic bounds. -/

variable (k : Type*) {R ι κ : Type*} [CommRing k] [CommRing R] [Algebra k R]

theorem relativeLogarithmicDerivations_congr_of_logarithmic
    (w : ι → R) (v : κ → R) (h : LogarithmicDerivation.Construction.logarithmicDerivations w = LogarithmicDerivation.Construction.logarithmicDerivations v) :
    LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w = LogarithmicIdeal.Construction.relativeLogarithmicDerivations k v := by
  ext D
  change D.restrictScalars ℤ ∈ LogarithmicDerivation.Construction.logarithmicDerivations w ↔
    D.restrictScalars ℤ ∈ LogarithmicDerivation.Construction.logarithmicDerivations v
  rw [h]

theorem iteratedRelativeLogarithmicDifferentialIdeal_congr_derivations
    (w : ι → R) (v : κ → R)
    (h : LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w = LogarithmicIdeal.Construction.relativeLogarithmicDerivations k v)
    (J : Ideal R) (n : ℕ) :
    LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J n =
      LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k v J n := by
  have hfirst (L : Ideal R) : LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k w L =
      LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k v L := by
    unfold LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal
    rw [h]
  induction n generalizing J with
  | zero => rfl
  | succ n ih =>
    change LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w
      (LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k w J) n = _
    rw [hfirst]
    exact ih (LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k v J)

theorem relativeLogarithmicDerivations_coordinate_boundary_reindex
    {σ : Type*} [DecidableEq σ] (x : σ → R) (B : Finset σ) (i : σ) :
    LogarithmicIdeal.Construction.relativeLogarithmicDerivations k
      (fun j : Option B => Option.elim j (x i) (fun a => if a.val = i then 1 else x a.val)) =
      LogarithmicIdeal.Construction.relativeLogarithmicDerivations k (fun j : (insert i B : Finset σ) => x j.val) :=
  relativeLogarithmicDerivations_congr_of_logarithmic k _ _
    (LogarithmicBoundaryReindex.Construction.logarithmicDerivations_coordinate_boundary_reindex x B i)

theorem relativeLogarithmicDerivations_remove_unit_components
    {σ : Type*} [DecidableEq σ] (w : σ → R) (B C : Finset σ)
    (hCB : C ⊆ B) (hunit : ∀ i ∈ B, i ∉ C → IsUnit (w i)) :
    LogarithmicIdeal.Construction.relativeLogarithmicDerivations k (fun i : B => w i.val) =
      LogarithmicIdeal.Construction.relativeLogarithmicDerivations k (fun i : C => w i.val) :=
  relativeLogarithmicDerivations_congr_of_logarithmic k _ _
    (LogarithmicEtaleMap.Construction.logarithmicDerivations_remove_unit_components w B C hCB hunit)

variable {S : Type*} [CommRing S] [Algebra k S] [Algebra R S]
  [IsScalarTower k R S] [Algebra.FormallyEtale R S]

theorem extendEtaleRingDerivation_relative_logarithmic
    (w : ι → R) (D : LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w) :
    Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) D.val ∈
      LogarithmicIdeal.Construction.relativeLogarithmicDerivations k (fun i => algebraMap R S (w i)) := by
  intro i
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp (D.property i)
  rw [Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, ht, map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem firstRelativeLogarithmicDifferentialIdeal_map_le (w : ι → R) (J : Ideal R) :
    (LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k w J).map (algebraMap R S) ≤
      LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k (fun i => algebraMap R S (w i))
        (J.map (algebraMap R S)) := by
  rw [Ideal.map_le_iff_le_comap]
  apply sup_le
  · intro p hp
    exact LogarithmicIdeal.Construction.le_firstRelativeLogarithmicDifferentialIdeal k _ _ (Ideal.mem_map_of_mem _ hp)
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨D, p⟩, rfl⟩
    change algebraMap R S (D.val p.val) ∈
      LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k (fun i => algebraMap R S (w i))
        (J.map (algebraMap R S))
    rw [← Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap (S := S) D.val p.val]
    exact LogarithmicIdeal.Construction.relative_logarithmic_derivation_mem_first k _ _
      ⟨Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) D.val,
        extendEtaleRingDerivation_relative_logarithmic k w D⟩ (Ideal.mem_map_of_mem _ p.property)

theorem iteratedRelativeLogarithmicDifferentialIdeal_map_le (w : ι → R) (J : Ideal R) (n : ℕ) :
    (LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J n).map (algebraMap R S) ≤
      LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k (fun i => algebraMap R S (w i))
        (J.map (algebraMap R S)) n := by
  induction n generalizing J with
  | zero => exact le_rfl
  | succ n ih =>
    exact (ih (LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k w J)).trans
      (LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal_mono k _ n
        (firstRelativeLogarithmicDifferentialIdeal_map_le (S := S) k w J))

theorem relative_logarithmic_order_bound_map (w : ι → R) (J : Ideal R) (n : ℕ)
    (h : LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J n = ⊤) :
    LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k (fun i => algebraMap R S (w i))
      (J.map (algebraMap R S)) n = ⊤ := by
  have hle := iteratedRelativeLogarithmicDifferentialIdeal_map_le (S := S) k w J n
  rw [h, Ideal.map_top] at hle
  exact top_le_iff.mp hle

end

/-! Surjective boundary reindexing leaves all relative logarithmic differential ideals unchanged. -/

variable (k : Type*) {R ι κ : Type*} [CommRing k] [CommRing R] [Algebra k R]

theorem relativeLogarithmicDerivations_surjective_reindex
    (w : ι → R) (e : κ → ι) (he : Function.Surjective e) :
    LogarithmicIdeal.Construction.relativeLogarithmicDerivations k (fun j => w (e j)) = LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w := by
  ext D
  change (∀ j, D (w (e j)) ∈ Ideal.span {w (e j)}) ↔
    ∀ i, D (w i) ∈ Ideal.span {w i}
  constructor
  · intro h i
    obtain ⟨j, rfl⟩ := he i
    exact h j
  · intro h j
    exact h (e j)

theorem iteratedRelativeLogarithmicDifferentialIdeal_surjective_reindex
    (w : ι → R) (e : κ → ι) (he : Function.Surjective e) (J : Ideal R) (n : ℕ) :
    LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k (fun j => w (e j)) J n =
      LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J n :=
  iteratedRelativeLogarithmicDifferentialIdeal_congr_derivations k _ _
    (relativeLogarithmicDerivations_surjective_reindex k w e he) J n

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicBoundary.Construction
