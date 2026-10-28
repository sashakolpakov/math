import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutUniversal
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBlocks
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutReplaceConstraints

namespace OAI.Algorithms

/-! Bridges for an explicit runtime enumeration of raw integer rows.
The enumeration need not agree with the semantic `Fintype.equivFin` order. -/
namespace SubexponentialSAT.SqrtLog.LayoutExactBuckets

open scoped BigOperators

variable {J K H V I : Type*} [Fintype V] [Fintype K]

omit [Fintype V] in
theorem rationalRowSpan_reindex_left (C : J → V → ℤ) (A : K → V → ℤ)
    (hspan : RationalRowSpan C A) (e : H → J) :
    RationalRowSpan (fun h => C (e h)) A := fun h => hspan (e h)

omit [Fintype V] in
theorem rationalRowSpan_of_surjective (C : J → V → ℤ) (e : K → J)
    (he : Function.Surjective e) : RationalRowSpan C (fun k => C (e k)) := by
  classical
  intro j
  obtain ⟨k, rfl⟩ := he j
  refine ⟨Pi.single k 1, ?_⟩
  intro v
  simp [Pi.single_apply]

omit [Fintype V] in
theorem rationalRowSpan_pullback [Fintype I] [DecidableEq V]
    (owner : I → V) (C : J → I → ℤ) (A : K → I → ℤ)
    (hspan : RationalRowSpan C A) :
    RationalRowSpan (pulledConstraints owner C) (pulledConstraints owner A) := by
  classical
  intro j
  obtain ⟨c, hc⟩ := hspan j
  refine ⟨c, ?_⟩
  intro v
  simp only [pulledConstraints, LayoutPullback.row, Int.cast_sum, Int.cast_ite,
    Int.cast_zero]
  simp_rw [hc]
  calc
    _ = ∑ i, ∑ k, c k * (if owner i = v then (A k i : ℚ) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : owner i = v <;> simp [h]
    _ = ∑ k, ∑ i, c k * (if owner i = v then (A k i : ℚ) else 0) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      exact (Finset.mul_sum Finset.univ
        (fun i => if owner i = v then (A k i : ℚ) else 0) (c k)).symm

end SubexponentialSAT.SqrtLog.LayoutExactBuckets

namespace SubexponentialSAT.SqrtLog.LayoutUniversal

open SubexponentialSAT.MulticolorTypes LayoutExactBuckets

variable {r Q R : ℕ} {O : Type*} [CommRing O] {node : Fin Q → O}

/-- A certificate against the raw joint-indexed matrix suffices for any
runtime-selected constraints on the semantic universal layout. -/
theorem data_rationalRowSpan (A : ℕ) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node)
    (t : Fin Q) (g : Fin r) {K : Type*} [Fintype K]
    (rows : K → Head t g → ℤ)
    (hspan : RationalRowSpan (constraints A R t g) rows) :
    RationalRowSpan ((data A R denom hdenom units).constraints t g) rows :=
  fun j => hspan ((Fintype.equivFin (Joint t g (0 : Fin 1))).symm j)

end SubexponentialSAT.SqrtLog.LayoutUniversal

end OAI.Algorithms
