import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechSupportContraction

/-! # Ordered Cech Zero Cycles -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechZeroCycles

noncomputable section

/-! Degree-zero cycles with empty required support are constant cochains. -/

open _root_.AlgebraicGeometry
universe u v
variable (R : Type u) [CommRing R] {ι : Type v} [LinearOrder ι]

def orderedSupportSingleton (i : ι) : OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 :=
  ⟨![i], by
    apply Fin.strictMono_iff_lt_succ.2
    intro k
    exact Fin.elim0 k⟩

def orderedSupportPair (i j : ι) (hij : i < j) : OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 1 :=
  ⟨![i, j], by
    apply Fin.strictMono_iff_lt_succ.2
    intro k
    fin_cases k
    exact hij⟩

theorem orderedSupportSingleton_of_index (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0) :
    orderedSupportSingleton (a.1 0) = a := by
  apply Subtype.ext
  funext k
  fin_cases k
  rfl

theorem orderedSupportPair_delete_zero (i j : ι) (hij : i < j) :
    (orderedSupportPair i j hij).delete 0 = orderedSupportSingleton j := by
  apply Subtype.ext
  funext k
  fin_cases k
  rfl

theorem orderedSupportPair_delete_one (i j : ι) (hij : i < j) :
    (orderedSupportPair i j hij).delete 1 = orderedSupportSingleton i := by
  apply Subtype.ext
  funext k
  fin_cases k
  rfl

theorem orderedSupportZeroCycle_pair
    (s : (OrderedCechSupportContraction.orderedCechSupportDifferential R (∅ : Set ι) 0).ker)
    (i j : ι) (hij : i < j) :
    s.val.val (orderedSupportSingleton j) = s.val.val (orderedSupportSingleton i) := by
  have h := congrArg (fun z => z.val (orderedSupportPair i j hij)) s.property
  change (∑ k : Fin 2, (-1 : R) ^ (k : ℕ) *
    s.val.val ((orderedSupportPair i j hij).delete k)) = 0 at h
  simp only [Fin.sum_univ_two, Fin.val_zero, pow_zero, one_mul,
    orderedSupportPair_delete_zero, Fin.val_one, pow_one,
    orderedSupportPair_delete_one, neg_one_mul] at h
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using h)

theorem orderedSupportZeroCycle_constant
    (s : (OrderedCechSupportContraction.orderedCechSupportDifferential R (∅ : Set ι) 0).ker)
    (i : ι) (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0) :
    s.val.val a = s.val.val (orderedSupportSingleton i) := by
  rw [← orderedSupportSingleton_of_index a]
  rcases lt_trichotomy i (a.1 0) with h | h | h
  · exact orderedSupportZeroCycle_pair R s i (a.1 0) h
  · rw [h]
  · exact (orderedSupportZeroCycle_pair R s (a.1 0) i h).symm

def orderedConstantZeroCycle (r : R) :
    (OrderedCechSupportContraction.orderedCechSupportDifferential R (∅ : Set ι) 0).ker :=
  ⟨⟨fun _ => r, fun _ h => (h (Set.empty_subset _)).elim⟩, by
    apply Subtype.ext
    funext a
    change (∑ k : Fin 2, (-1 : R) ^ (k : ℕ) * r) = 0
    simp [Fin.sum_univ_succ]⟩

def orderedZeroCycleEvaluation (i : ι) :
    (OrderedCechSupportContraction.orderedCechSupportDifferential R (∅ : Set ι) 0).ker →ₗ[R] R where
  toFun s := s.val.val (orderedSupportSingleton i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def orderedZeroCyclesEquiv (i : ι) :
    (OrderedCechSupportContraction.orderedCechSupportDifferential R (∅ : Set ι) 0).ker ≃ₗ[R] R :=
  LinearEquiv.ofBijective (orderedZeroCycleEvaluation R i) ⟨by
    intro s t h
    apply Subtype.ext
    apply Subtype.ext
    funext a
    rw [orderedSupportZeroCycle_constant R s i a,
      orderedSupportZeroCycle_constant R t i a]
    exact h,
    fun r => ⟨orderedConstantZeroCycle R r, rfl⟩⟩

def orderedEmptySupportCyclesEquiv (N : Set ι) (hN : N = ∅) (i : ι) :
    (OrderedCechSupportContraction.orderedCechSupportDifferential R N 0).ker ≃ₗ[R] R := by
  subst N
  exact orderedZeroCyclesEquiv R i

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechZeroCycles
