import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpWeightGather

namespace OAI.Algorithms

/-! Uniform polynomial bounds for current-exponent gathering. The parameter
bound is the retained moment condition, not an enumeration of assignments. -/

namespace SubexponentialSAT.SubexpSourceBounds

open scoped BigOperators

theorem words_length (xs : List ℕ) :
    (SubexpExponentGather.words xs).length = xs.sum + xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [SubexpExponentGather.words,List.flatMap_cons,List.length_append,
        Encoding.length_encodeNat,List.sum_cons,List.length_cons] at *
      omega

theorem skipCost_eq (xs : List ℕ) :
    SubexpExponentGather.skipCost xs = 2*xs.sum+4*xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [SubexpExponentGather.skipCost,List.map_cons,List.sum_cons,List.length_cons] at *
      omega

theorem retained_gatherBudget_le {D : ℕ} (a : Fin D → ℕ)
    (hdegree : (∑ i, a i) ≤ 2*D+1) (i : Fin D) :
    SubexpExponentGather.gatherBudget ((List.ofFn a).take i.val) (a i)
      ((List.ofFn a).drop (i.val+1)) ≤ 32*D^2+95*D+52 := by
  let xs := List.ofFn a
  have hsum : xs.sum ≤ 2*D+1 := by simpa only [xs,Fin.sum_ofFn] using hdegree
  have hlen : xs.length = D := List.length_ofFn
  have hi : a i ≤ 2*D+1 :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)).trans hdegree
  have hp := List.sum_take_add_sum_drop xs i.val
  have hs := List.sum_take_add_sum_drop xs (i.val+1)
  have hprefix : (xs.take i.val).sum ≤ 2*D+1 := by omega
  have hsuffix : (xs.drop (i.val+1)).sum ≤ 2*D+1 := by omega
  have hprefixLen : (xs.take i.val).length ≤ D := by simp only [List.length_take,hlen]; omega
  have hsuffixLen : (xs.drop (i.val+1)).length ≤ D := by simp only [List.length_drop,hlen]; omega
  have hmaster : (SubexpExponentGather.words
      ((xs.take i.val) ++ a i :: xs.drop (i.val+1))).length ≤ 3*D+1 := by
    rw [←SubexpExponentGather.ofFn_decomposition a i,words_length]
    change xs.sum + xs.length ≤ 3*D+1
    omega
  have hskip : SubexpExponentGather.skipCost (xs.take i.val) ≤ 8*D+2 := by
    rw [skipCost_eq]
    omega
  have htail : (SubexpExponentGather.words (xs.drop (i.val+1))).length ≤ 3*D+1 := by
    rw [words_length]
    omega
  have hquadratic : a i * (8*a i+10) ≤ (2*D+1)*(8*(2*D+1)+10) :=
    Nat.mul_le_mul hi (by omega)
  unfold SubexpExponentGather.gatherBudget
  change 7*(SubexpExponentGather.words ((xs.take i.val) ++ a i :: xs.drop (i.val+1))).length+
    SubexpExponentGather.skipCost (xs.take i.val)+4*a i+
    2*(SubexpExponentGather.words (xs.drop (i.val+1))).length+a i*(8*a i+10)+19 ≤ _
  nlinarith

theorem retained_callbackBudget_le {D : ℕ} (a : Fin D → ℕ)
    (width target : List Bool) (hpad : width.length ≤ target.length)
    (hdegree : (∑ i, a i) ≤ 2*D+1) (i : Fin D) :
    SubexpWeightGather.callbackBudget a width target i ≤
      32*D^2+155*D+14*D*target.length+40*target.length+177 := by
  have hg := retained_gatherBudget_le a hdegree i
  have hi : i.val ≤ D := i.isLt.le
  have hn : a i ≤ 2*D+1 :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)).trans hdegree
  have hm : i.val*(14*width.length+10) ≤ D*(14*target.length+10) :=
    Nat.mul_le_mul hi (by omega)
  unfold SubexpWeightGather.callbackBudget
  nlinarith

theorem retained_supportBudget_le {D : ℕ} (a : Fin D → ℕ)
    (width target : List Bool) (hpad : width.length ≤ target.length)
    (hdegree : (∑ i, a i) ≤ 2*D+1) (support : List (Fin D)) (hn : support.Nodup) :
    SubexpWeightGather.supportBudget a width target support ≤
      D*(32*D^2+161*D+14*D*target.length+40*target.length+184) := by
  let K := 32*D^2+161*D+14*D*target.length+40*target.length+184
  have hpoint : ∀ i : Fin D, 6*i.val+SubexpWeightGather.callbackBudget a width target i+7 ≤ K := by
    intro i
    have h := retained_callbackBudget_le a width target hpad hdegree i
    have hi := i.isLt.le
    dsimp [K]
    omega
  have hlist : ∀ xs : List (Fin D), SubexpWeightGather.supportBudget a width target xs ≤ xs.length*K := by
    intro xs
    induction xs with
    | nil => simp [SubexpWeightGather.supportBudget]
    | cons i xs ih =>
        have h := hpoint i
        simp only [SubexpWeightGather.supportBudget,List.map_cons,List.sum_cons,List.length_cons] at *
        nlinarith
  have hcount : support.length ≤ D := by simpa using hn.length_le_card
  exact (hlist support).trans (Nat.mul_le_mul_right K hcount)

end SubexponentialSAT.SubexpSourceBounds

end OAI.Algorithms
