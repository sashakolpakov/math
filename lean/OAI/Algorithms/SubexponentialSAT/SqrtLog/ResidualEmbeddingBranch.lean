import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbeddingStored
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceNeutral

namespace OAI.Algorithms

/-! Fixed high-coordinate branches and original ambient coordinate labels.
Only free assignments are summed inside one branch. -/
namespace SubexponentialSAT.SqrtLog.ResidualEmbedding

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Free (H : Finset V) := {v : V // v ∉ H}

def inclusion (H : Finset V) : Free H ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

def freeVars (H : Finset V) : Finset V := Finset.univ.filter (fun v => v ∉ H)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem inclusion_apply (H : Finset V) (v : Free H) : inclusion H v = v.val := rfl

@[simp] theorem free_univ_map (H : Finset V) :
    (Finset.univ : Finset (Free H)).map (inclusion H) = freeVars H := by
  ext v
  simp [freeVars, inclusion]

omit [Fintype V] [DecidableEq V] in
theorem map_disjoint_high (H : Finset V) (s : Finset (Free H)) :
    Disjoint (s.map (inclusion H)) H := by
  apply Finset.disjoint_left.mpr
  intro v hv hH
  obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
  exact u.property hH

omit [Fintype V] [DecidableEq V] in
theorem no_map_of_high_mem (H : Finset V) (s : Finset V)
    (hs : ∃ v ∈ s, v ∈ H) : ¬ ∃ a : Finset (Free H), a.map (inclusion H) = s := by
  rintro ⟨a, rfl⟩
  obtain ⟨v, hv, hH⟩ := hs
  exact Finset.disjoint_left.mp (map_disjoint_high H a) hv hH

noncomputable section
variable {R : Type*} [CommSemiring R]

omit [Fintype V] in
theorem high_support_zero (H : Finset V) (s : Finset V)
    (hs : ∃ v ∈ s, v ∈ H) (f : Jet (Free H) R) :
    Moments.jetCoeff ⟨s⟩ (jet (inclusion H) f) = 0 :=
  jetCoeff_jet_zero (inclusion H) s (no_map_of_high_mem H s hs) f

def ambientStored (H : Finset V) {t J : ℕ}
    (a : Moments.Stored (R := R) (Finset.univ : Finset (Free H)) t J) :
    Moments.Stored (R := R) (Finset.univ : Finset V) t J :=
  weaken (Finset.subset_univ _) (stored (inclusion H) a)

@[simp] theorem ambientStored_denote (H : Finset V) {t J : ℕ}
    (a : Moments.Stored (R := R) (Finset.univ : Finset (Free H)) t J) :
    (ambientStored H a).denote = jet (inclusion H) a.denote := by
  simp [ambientStored]

omit [CommSemiring R] in
@[simp] theorem ambientStored_length (H : Finset V) {t J : ℕ}
    (a : Moments.Stored (R := R) (Finset.univ : Finset (Free H)) t J) :
    (ambientStored H a).data.length = a.data.length := by
  exact data_length (inclusion H) a.data

omit [CommSemiring R] in
theorem ambientStored_free_valid (H : Finset V) {t J : ℕ}
    (a : Moments.Stored (R := R) (Finset.univ : Finset (Free H)) t J) :
    Sparse.ValidData (freeVars H) t J (ambientStored H a).data := by
  simpa only [ambientStored, free_univ_map] using
    (weaken_data_valid (Finset.subset_univ _) (stored (inclusion H) a))

end

/-- Compatibility with the fixed values of the high variables. -/
abbrev Branch (H : Finset V) (a : H → Bool) :=
  {x : V → Bool // ∀ v : H, x v.val = a v}

def branchEquiv (H : Finset V) (a : H → Bool) : (Free H → Bool) ≃ Branch H a where
  toFun b := ⟨HighIncidence.glue H a b, by
    intro v
    simp [HighIncidence.glue, v.property]⟩
  invFun x v := x.val v.val
  left_inv b := by
    funext v
    simp [HighIncidence.glue, v.property]
  right_inv x := by
    apply Subtype.ext
    funext v
    by_cases h : v ∈ H
    · simpa [HighIncidence.glue, h] using (x.property ⟨v, h⟩).symm
    · simp [HighIncidence.glue, h]

theorem sum_branch {M : Type*} [AddCommMonoid M] (H : Finset V) (a : H → Bool)
    (f : (V → Bool) → M) :
    (∑ b : Free H → Bool, f (HighIncidence.glue H a b)) =
      ∑ x : Branch H a, f x.val :=
  Fintype.sum_equiv (branchEquiv H a) _ _ (fun _ => rfl)

theorem branch_card (H : Finset V) (a : H → Bool) :
    Fintype.card (Branch H a) = 2 ^ Fintype.card (Free H) := by
  rw [← Fintype.card_congr (branchEquiv H a)]
  simp

/-- The neutral factors are formed in the free universe; hence even an unused
high coordinate cannot create a neutral factor or an additional assignment. -/
theorem neutral_scope_avoids_high {E : Type*} [Fintype E] [DecidableEq E]
    (H : Finset V) (scope : E → Finset (Free H))
    (e : E ⊕ HighIncidence.uncovered scope) :
    Disjoint ((HighIncidence.neutralScope scope e).map (inclusion H)) H :=
  map_disjoint_high H _

end SubexponentialSAT.SqrtLog.ResidualEmbedding

end OAI.Algorithms
