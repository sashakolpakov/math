import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompactRestriction
import Mathlib.Topology.Compactness.SigmaCompact

/-! # Spatial Exhaustion -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SpatialExhaustion.Cycles.SpatialSupport

noncomputable section

/-!
# Reconstructing spatially locally finite coefficients along a compact exhaustion

Finite coefficient families supported on the images meeting successive compact
sets form a coherent system when their already-visible coefficients agree.
Such systems are exactly spatially locally finite coefficient functions. The
inverse is constructed from stable coefficients, and local finiteness follows
from a compact stage that is a neighborhood of each point.
-/

open Set Function Filter
open scoped Classical _root_.Topology

variable {X ι : Type*} [TopologicalSpace X]
variable {R : Type*} [Semiring R]

/-- Meeting a stage is preserved when the stage increases. -/
theorem meets_exhaustion_mono (image : ι → Set X) (K : CompactExhaustion X)
    {m n : ℕ} (hmn : m ≤ n) (i : ι) (hi : (image i ∩ K m).Nonempty) :
    (image i ∩ K n).Nonempty := by
  obtain ⟨x, hxi, hxK⟩ := hi
  exact ⟨x, hxi, K.subset hmn hxK⟩

/-- Every nonempty indexed image meets a stage of a genuine compact exhaustion. -/
theorem exists_meeting_stage (image : ι → Set X) (K : CompactExhaustion X)
    (hne : ∀ i, (image i).Nonempty) (i : ι) :
    ∃ m, (image i ∩ K m).Nonempty := by
  obtain ⟨x, hx⟩ := hne i
  obtain ⟨m, hm⟩ := K.exists_mem x
  exact ⟨m, x, hx, hm⟩

/-- The first stage at which an indexed image is visible. -/
def firstMeetingStage (image : ι → Set X) (K : CompactExhaustion X)
    (hne : ∀ i, (image i).Nonempty) (i : ι) : ℕ :=
  Nat.find (exists_meeting_stage image K hne i)

theorem firstMeetingStage_spec (image : ι → Set X) (K : CompactExhaustion X)
    (hne : ∀ i, (image i).Nonempty) (i : ι) :
    (image i ∩ K (firstMeetingStage image K hne i)).Nonempty :=
  Nat.find_spec (exists_meeting_stage image K hne i)

theorem firstMeetingStage_le (image : ι → Set X) (K : CompactExhaustion X)
    (hne : ∀ i, (image i).Nonempty) (i : ι) (m : ℕ)
    (hi : (image i ∩ K m).Nonempty) : firstMeetingStage image K hne i ≤ m :=
  Nat.find_min' (exists_meeting_stage image K hne i) hi

/-- Finite families supported on the images visible at each stage, whose
coefficients agree as soon as an image is visible. -/
def coherentExhaustionCoefficients (R : Type*) [Semiring R]
    (image : ι → Set X) (K : CompactExhaustion X) : Submodule R (ℕ → ι →₀ R) where
  carrier := {c | (∀ m i, ¬ (image i ∩ K m).Nonempty → c m i = 0) ∧
    ∀ m i, (image i ∩ K m).Nonempty → c (m + 1) i = c m i}
  zero_mem' := by constructor <;> intros <;> rfl
  add_mem' := by
    rintro c d ⟨hc, hc'⟩ ⟨hd, hd'⟩
    constructor
    · intro m i hi
      change c m i + d m i = 0
      rw [hc m i hi, hd m i hi, add_zero]
    · intro m i hi
      change c (m + 1) i + d (m + 1) i = c m i + d m i
      rw [hc' m i hi, hd' m i hi]
  smul_mem' := by
    rintro r c ⟨hc, hc'⟩
    constructor
    · intro m i hi
      change r • c m i = 0
      rw [hc m i hi, smul_zero]
    · intro m i hi
      change r • c (m + 1) i = r • c m i
      rw [hc' m i hi]

/-- Consecutive coherence gives stability between any two visible stages. -/
theorem coherentExhaustionCoefficients_stable (image : ι → Set X)
    (K : CompactExhaustion X) (c : coherentExhaustionCoefficients R image K)
    {m n : ℕ} (hmn : m ≤ n) (i : ι) (hi : (image i ∩ K m).Nonempty) :
    c.val n i = c.val m i := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      exact (c.property.2 n i (meets_exhaustion_mono image K hmn i hi)).trans ih

/-- The coefficient reconstructed from the first visible stage. -/
def reconstructedCoefficient (image : ι → Set X) (K : CompactExhaustion X)
    (hne : ∀ i, (image i).Nonempty) (c : coherentExhaustionCoefficients R image K)
    (i : ι) : R := c.val (firstMeetingStage image K hne i) i

/-- The reconstructed coefficient equals its value at every visible stage. -/
theorem reconstructedCoefficient_agrees (image : ι → Set X) (K : CompactExhaustion X)
    (hne : ∀ i, (image i).Nonempty) (c : coherentExhaustionCoefficients R image K)
    (m : ℕ) (i : ι) (hi : (image i ∩ K m).Nonempty) :
    reconstructedCoefficient image K hne c i = c.val m i :=
  (coherentExhaustionCoefficients_stable image K c
    (firstMeetingStage_le image K hne i m hi) i
    (firstMeetingStage_spec image K hne i)).symm

/-- A compact stage containing a neighborhood bounds all reconstructed
nonzero images meeting that neighborhood by a finite stage support. -/
theorem reconstructedCoefficient_locallyFinite (image : ι → Set X)
    (K : CompactExhaustion X) (hne : ∀ i, (image i).Nonempty)
    (c : coherentExhaustionCoefficients R image K) :
    LocallyFiniteChains.Cycles.SpatialSupport.IsLocallyFinite image (reconstructedCoefficient image K hne c) := by
  intro x
  obtain ⟨m, hm⟩ := K.exists_mem_nhds x
  refine ⟨K m, hm, (c.val m).support.finite_toSet.subset ?_⟩
  rintro i ⟨y, ⟨hci, hyi⟩, hyK⟩
  apply Finsupp.mem_support_iff.mpr
  intro hz
  exact hci ((reconstructedCoefficient_agrees image K hne c m i ⟨y, hyi, hyK⟩).trans hz)

/-- Reconstruction produces an actual spatially locally finite coefficient function. -/
def fromExhaustionCoefficients (image : ι → Set X) (K : CompactExhaustion X)
    (hne : ∀ i, (image i).Nonempty) :
    coherentExhaustionCoefficients R image K →ₗ[R] LocallyFiniteChains.Cycles.SpatialSupport.module R image where
  toFun c := ⟨reconstructedCoefficient image K hne c,
    reconstructedCoefficient_locallyFinite image K hne c⟩
  map_add' c d := by
    apply Subtype.ext
    funext i
    rfl
  map_smul' r c := by
    apply Subtype.ext
    funext i
    rfl

@[simp]
theorem fromExhaustionCoefficients_apply (image : ι → Set X) (K : CompactExhaustion X)
    (hne : ∀ i, (image i).Nonempty) (c : coherentExhaustionCoefficients R image K) (i : ι) :
    fromExhaustionCoefficients image K hne c i =
      c.val (firstMeetingStage image K hne i) i := rfl

/-- Compact truncations of a spatially locally finite function form a coherent
family of actual finitely supported coefficients. -/
def toExhaustionCoefficients (image : ι → Set X) (K : CompactExhaustion X) :
    LocallyFiniteChains.Cycles.SpatialSupport.module R image →ₗ[R] coherentExhaustionCoefficients R image K where
  toFun c := ⟨fun m => LocallyFiniteCompactRestriction.Cycles.SpatialSupport.compactTruncation image (K m) (K.isCompact m) c, by
    constructor
    · intro m i hi
      rw [LocallyFiniteCompactRestriction.Cycles.SpatialSupport.compactTruncation_apply, ite_eq_right hi]
    · intro m i hi
      rw [LocallyFiniteCompactRestriction.Cycles.SpatialSupport.compactTruncation_apply,
        ite_eq_left (meets_exhaustion_mono image K (Nat.le_succ m) i hi),
        LocallyFiniteCompactRestriction.Cycles.SpatialSupport.compactTruncation_apply, ite_eq_left hi]⟩
  map_add' c d := by
    apply Subtype.ext
    funext m
    exact (LocallyFiniteCompactRestriction.Cycles.SpatialSupport.compactTruncation image (K m) (K.isCompact m)).map_add c d
  map_smul' r c := by
    apply Subtype.ext
    funext m
    exact (LocallyFiniteCompactRestriction.Cycles.SpatialSupport.compactTruncation image (K m) (K.isCompact m)).map_smul r c

@[simp]
theorem toExhaustionCoefficients_apply (image : ι → Set X) (K : CompactExhaustion X)
    (c : LocallyFiniteChains.Cycles.SpatialSupport.module R image) (m : ℕ) (i : ι) :
    (toExhaustionCoefficients image K c).val m i =
      if (image i ∩ K m).Nonempty then c i else 0 := rfl

theorem fromExhaustionCoefficients_to (image : ι → Set X) (K : CompactExhaustion X)
    (hne : ∀ i, (image i).Nonempty) (c : LocallyFiniteChains.Cycles.SpatialSupport.module R image) :
    fromExhaustionCoefficients image K hne (toExhaustionCoefficients image K c) = c := by
  apply Subtype.ext
  funext i
  rw [fromExhaustionCoefficients_apply, toExhaustionCoefficients_apply,
    ite_eq_left (firstMeetingStage_spec image K hne i)]

theorem toExhaustionCoefficients_from (image : ι → Set X) (K : CompactExhaustion X)
    (hne : ∀ i, (image i).Nonempty) (c : coherentExhaustionCoefficients R image K) :
    toExhaustionCoefficients image K (fromExhaustionCoefficients image K hne c) = c := by
  apply Subtype.ext
  funext m
  apply Finsupp.ext
  intro i
  rw [toExhaustionCoefficients_apply]
  by_cases hi : (image i ∩ K m).Nonempty
  · rw [ite_eq_left hi]
    exact reconstructedCoefficient_agrees image K hne c m i hi
  · rw [ite_eq_right hi]
    exact (c.property.1 m i hi).symm

/-- Stable finite stage coefficients are equivalent to actual spatially
locally finite coefficients. Both maps preserve every visible coefficient. -/
def exhaustionCoefficientsEquiv (image : ι → Set X) (K : CompactExhaustion X)
    (hne : ∀ i, (image i).Nonempty) :
    LocallyFiniteChains.Cycles.SpatialSupport.module R image ≃ₗ[R] coherentExhaustionCoefficients R image K where
  toFun := toExhaustionCoefficients image K
  invFun := fromExhaustionCoefficients image K hne
  left_inv := fromExhaustionCoefficients_to image K hne
  right_inv := toExhaustionCoefficients_from image K hne
  map_add' := (toExhaustionCoefficients image K).map_add
  map_smul' := (toExhaustionCoefficients image K).map_smul

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SpatialExhaustion.Cycles.SpatialSupport
