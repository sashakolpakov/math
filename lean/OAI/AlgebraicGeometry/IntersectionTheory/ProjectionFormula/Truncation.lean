import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.StalkDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.Dimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.TorLength

/-! # Truncation -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Truncation

noncomputable section

/-! ThomClass's specified upper limit includes every nonzero local Tor term.
The same intersection multiplicity may therefore be computed with any
upper limit at least the smooth relative dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem localTorLength_eq_zero (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (A B : IrreducibleCloseds X.carrier)
    (x : X.carrier) (hxA : x ∈ (A : Set X.carrier)) (hxB : x ∈ (B : Set X.carrier))
    (i : ℕ) (hi : m < i) : CycleClass.Thom.IntersectionGeometry.localTorLength X.carrier A B x hxA hxB i = 0 :=
  Smooth.StalkDimension.stalk_tor_length_zero X.structureMap m x _ _ i hi

theorem localTorLength_eq_zero_above_ambient (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (A B : IrreducibleCloseds X.carrier)
    (x : X.carrier) (hxA : x ∈ (A : Set X.carrier)) (hxB : x ∈ (B : Set X.carrier))
    (i : ℕ) (hi : X.ambientDimension < i) : CycleClass.Thom.IntersectionGeometry.localTorLength X.carrier A B x hxA hxB i = 0 :=
  localTorLength_eq_zero X m A B x hxA hxB i
    ((Projective.Dimension.relativeDimension_le X m x).trans_lt hi)

theorem local_euler_sum_stable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (A B : IrreducibleCloseds X.carrier)
    (x : X.carrier) (hxA : x ∈ (A : Set X.carrier)) (hxB : x ∈ (B : Set X.carrier))
    (d : ℕ) (hd : m ≤ d) :
    (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
      (CycleClass.Thom.IntersectionGeometry.localTorLength X.carrier A B x hxA hxB i).toNat) =
    ∑ i ∈ Finset.range (m + 1), (-1 : ℚ) ^ i *
      (CycleClass.Thom.IntersectionGeometry.localTorLength X.carrier A B x hxA hxB i).toNat := by
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hd 1))
  intro i _ hi
  have him : m < i := by simp only [Finset.mem_range] at hi; omega
  simp [localTorLength_eq_zero X m A B x hxA hxB i him]

theorem intersectionMultiplicity_eq_relative_sum (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (A B C : IrreducibleCloseds X.carrier)
    (hxA : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (A : Set X.carrier))
    (hxB : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (B : Set X.carrier)) :
    CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A B C =
      ∑ i ∈ Finset.range (m + 1), (-1 : ℚ) ^ i *
        (CycleClass.Thom.IntersectionGeometry.localTorLength X.carrier A B (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxA hxB i).toNat := by
  rw [CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity, dite_eq_left ⟨hxA, hxB⟩]
  exact local_euler_sum_stable X m A B _ hxA hxB X.ambientDimension
    (Projective.Dimension.relativeDimension_le X m (CycleClass.Thom.IntersectionGeometry.supportPoint C))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Truncation
