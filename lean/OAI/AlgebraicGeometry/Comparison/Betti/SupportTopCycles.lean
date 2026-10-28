import OAI.AlgebraicGeometry.Comparison.Betti.SupportTopCochains
import OAI.AlgebraicGeometry.Comparison.Betti.SupportedCochainSorting

/-! # Support Top Cycles -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SupportTopCycles.Cech

noncomputable section

/-! Top-degree full-support cycles are exactly one copy of the additive coefficient group. -/

variable {V : Type} [AddCommGroup V]

theorem fullSupportTopCycle_sorted (n : ℕ)
    (s : SupportedCochains.Cech.supportedCechCochains V (Finset.univ : Finset (Fin (n + 1))) n)
    (hs : SupportedCochains.Cech.supportedCechDifferential Finset.univ n s = 0) :
    SupportedCochainSorting.Cech.supportedCechSorting Finset.univ n s = s := by
  cases n with
  | zero => exact SupportedCochainSorting.Cech.supportedCechSorting_zero_degree Finset.univ s
  | succ q =>
    have h := SupportedCochainSorting.Cech.supportedCechSorting_cycle Finset.univ q s hs
    have hH : SupportedCochainSorting.Cech.supportedCechSortingHomotopy Finset.univ q s = 0 :=
      SupportTopCochains.Cech.fullSupportCochain_zero_of_lt q (by simp) _
    rw [hH, map_zero] at h
    exact sub_eq_zero.mp h.symm

theorem fullSupportTopSorting_cycle (n : ℕ)
    (s : SupportedCochains.Cech.supportedCechCochains V (Finset.univ : Finset (Fin (n + 1))) n) :
    SupportedCochains.Cech.supportedCechDifferential Finset.univ n (SupportedCochainSorting.Cech.supportedCechSorting Finset.univ n s) = 0 := by
  rw [SupportedCochainSorting.Cech.supportedCechSorting_differential]
  exact SupportCochainVanishing.Cech.fullSupportSorting_zero (n + 1) (by simp) _

theorem fullSupportTopCycle_ext (n : ℕ)
    (s t : SupportedCochains.Cech.supportedCechCochains V (Finset.univ : Finset (Fin (n + 1))) n)
    (hs : SupportedCochains.Cech.supportedCechDifferential Finset.univ n s = 0)
    (ht : SupportedCochains.Cech.supportedCechDifferential Finset.univ n t = 0) (h : s.val id = t.val id) : s = t :=
  (fullSupportTopCycle_sorted n s hs).symm.trans
    ((SupportTopCochains.Cech.fullSupportTopSorting_ext n s t h).trans (fullSupportTopCycle_sorted n t ht))

def fullSupportTopSeed (n : ℕ) (v : V) :
    SupportedCochains.Cech.supportedCechCochains V (Finset.univ : Finset (Fin (n + 1))) n :=
  ⟨fun t => if t = id then v else 0, fun t ht => by
    have hne : t ≠ id := by
      intro h
      subst t
      apply ht
      intro i _
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    exact ite_eq_right hne⟩

theorem fullSupportTopSeed_id (n : ℕ) (v : V) : (fullSupportTopSeed n v).val id = v :=
  ite_eq_left rfl

def fullSupportTopCycleMap (n : ℕ) :
    V →+ (SupportedCochains.Cech.supportedCechDifferential (V := V) (Finset.univ : Finset (Fin (n + 1))) n).ker where
  toFun v := ⟨SupportedCochainSorting.Cech.supportedCechSorting Finset.univ n (fullSupportTopSeed n v),
    fullSupportTopSorting_cycle n _⟩
  map_zero' := by
    apply Subtype.ext
    apply fullSupportTopCycle_ext n
    · exact fullSupportTopSorting_cycle n _
    · exact map_zero _
    · rw [SupportTopCochains.Cech.fullSupportTopSorting_id, fullSupportTopSeed_id]
      rfl
  map_add' v w := by
    apply Subtype.ext
    apply fullSupportTopCycle_ext n
    · exact fullSupportTopSorting_cycle n _
    · change SupportedCochains.Cech.supportedCechDifferential Finset.univ n
        (SupportedCochainSorting.Cech.supportedCechSorting Finset.univ n (fullSupportTopSeed n v) +
          SupportedCochainSorting.Cech.supportedCechSorting Finset.univ n (fullSupportTopSeed n w)) = 0
      rw [map_add, fullSupportTopSorting_cycle, fullSupportTopSorting_cycle, add_zero]
    · change (SupportedCochainSorting.Cech.supportedCechSorting Finset.univ n (fullSupportTopSeed n (v + w))).val id =
        (SupportedCochainSorting.Cech.supportedCechSorting Finset.univ n (fullSupportTopSeed n v)).val id +
          (SupportedCochainSorting.Cech.supportedCechSorting Finset.univ n (fullSupportTopSeed n w)).val id
      rw [SupportTopCochains.Cech.fullSupportTopSorting_id, SupportTopCochains.Cech.fullSupportTopSorting_id, SupportTopCochains.Cech.fullSupportTopSorting_id,
        fullSupportTopSeed_id, fullSupportTopSeed_id, fullSupportTopSeed_id]

def fullSupportTopCyclesEquiv (n : ℕ) :
    (SupportedCochains.Cech.supportedCechDifferential (V := V) (Finset.univ : Finset (Fin (n + 1))) n).ker ≃+ V where
  toFun s := s.val.val id
  invFun v := fullSupportTopCycleMap n v
  left_inv s := by
    apply Subtype.ext
    apply fullSupportTopCycle_ext n
    · exact (fullSupportTopCycleMap n (s.val.val id)).property
    · exact s.property
    · exact (SupportTopCochains.Cech.fullSupportTopSorting_id n _).trans (fullSupportTopSeed_id n _)
  right_inv v := (SupportTopCochains.Cech.fullSupportTopSorting_id n _).trans (fullSupportTopSeed_id n v)
  map_add' _ _ := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.SupportTopCycles.Cech
