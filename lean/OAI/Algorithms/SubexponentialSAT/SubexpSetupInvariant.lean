import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStages

namespace OAI.Algorithms

/-! Value bookkeeping for the concrete setup sequence. These predicates only
describe encoded words; no predicate is used as an executable instruction. -/

namespace SubexponentialSAT.SubexpSetupProgram

theorem persistent_injective (c : Config) : Function.Injective (persistent c) := by
  intro i j h
  have hv := congrArg (fun x : Fin (stackCount c) => x.val) h
  apply Fin.ext
  simp only [persistent] at hv
  omega

@[simp] theorem persistent_eq_iff (c : Config) (i j : Fin 32) :
    persistent c i = persistent c j ↔ i = j := (persistent_injective c).eq_iff

def wordValue (c : Config) (a : SetupState c) (i : Fin 32) : ℕ :=
  BinaryArithmetic.toNat (a.stacks (persistent c i))

private def lookupWanted (blockSize : ℕ) (c : Config) (n : ℕ) (i : Fin 32) : ℕ :=
  match i.val with
  | 2 => n
  | 4 => SubexpPackingParameters.s n
  | 5 => SubexpPackingParameters.u n
  | 6 => SubexpPackingParameters.p n
  | 16 => DyadicSchedule.delta c.k c.T n
  | 17 => DyadicSchedule.Q n
  | 18 => blockSize
  | 19 => SubexpPackingParameters.D n
  | 20 => DyadicSchedule.Dstar c.k c.T n
  | 21 => SubexpPackingParameters.r n
  | 22 => SubexpPackingParameters.D n + 1
  | 23 => DyadicSchedule.M c.T n
  | 24 => DyadicSchedule.B c.k c.T n
  | 25 => DyadicSchedule.R c.k c.T n
  | 26 => DyadicSchedule.R c.k c.T n ^ 2
  | 27 => 16 * DyadicSchedule.Q n * DyadicSchedule.delta c.k c.T n * SubexpPackingParameters.s n
  | 28 => 32
  | 29 => SubexpPackingParameters.p n ^ 4 - 2
  | _ => 0

def wanted (c : Config) (n : ℕ) (i : Fin 32) : ℕ :=
  lookupWanted (DyadicSchedule.N c.k c.T n) c n i

private theorem lookupWanted_blockSize (blockSize : ℕ) (c : Config) (n : ℕ) :
    lookupWanted blockSize c n 18 = blockSize := rfl

/-- Resolve the finite slot lookup before substituting the growing power.
This keeps kernel conversion from unfolding the block-size calculation. -/
theorem wanted_blockSize (c : Config) (n : ℕ) :
    wanted c n 18 = DyadicSchedule.N c.k c.T n :=
  lookupWanted_blockSize (DyadicSchedule.N c.k c.T n) c n

def Known (c : Config) (n : ℕ) (ports : List (Fin 32)) (a : SetupState c) : Prop :=
  ∀ i ∈ ports, wordValue c a i = wanted c n i

def ScalarFrame (c : Config) (changed : List (Fin 32)) (a b : SetupState c) : Prop :=
  ∀ i, i ∉ changed → b.stacks (persistent c i) = a.stacks (persistent c i)

def PrefixFrame (c : Config) (a b : SetupState c) : Prop :=
  ∀ i : Fin 32, i.val < 6 → b.stacks (persistent c i) = a.stacks (persistent c i)

/-- All persistent slots outside the numerical output bank are retained. -/
def Retained (i : Fin 32) : Prop := i ≠ 6 ∧ (i.val < 16 ∨ 30 ≤ i.val)

def RetainedFrame (c : Config) (a b : SetupState c) : Prop :=
  ∀ i : Fin 32, Retained i → b.stacks (persistent c i) = a.stacks (persistent c i)

theorem preserves_scalarFrame (c : Config) (changed : List (Fin 32))
    (a b : SetupState c) (h : Preserves c (changed.map (persistent c)) a b) :
    ScalarFrame c changed a b := by
  intro i hi
  apply h.2 _ (persistent_protected c i)
  simpa only [List.mem_map, persistent_eq_iff, exists_eq_right] using hi

theorem scalarFrame_prefix (c : Config) (changed : List (Fin 32))
    (a b : SetupState c) (h : ScalarFrame c changed a b)
    (hc : ∀ i ∈ changed, 6 ≤ i.val) : PrefixFrame c a b := by
  intro i hi
  apply h i
  intro hm
  have := hc i hm
  omega

theorem prefixFrame_trans (c : Config) {a b d : SetupState c}
    (hab : PrefixFrame c a b) (hbd : PrefixFrame c b d) : PrefixFrame c a d := by
  intro i hi
  exact (hbd i hi).trans (hab i hi)

theorem scalarFrame_retained (c : Config) (changed : List (Fin 32))
    (a b : SetupState c) (h : ScalarFrame c changed a b)
    (hc : ∀ i ∈ changed, ¬ Retained i) : RetainedFrame c a b := by
  intro i hi
  exact h i (fun hm => hc i hm hi)

theorem retainedFrame_trans (c : Config) {a b d : SetupState c}
    (hab : RetainedFrame c a b) (hbd : RetainedFrame c b d) : RetainedFrame c a d := by
  intro i hi
  exact (hbd i hi).trans (hab i hi)

theorem retainedFrame_prefix (c : Config) {a b : SetupState c}
    (h : RetainedFrame c a b) : PrefixFrame c a b := by
  intro i hi
  apply h i
  constructor
  · intro he
    subst i
    change (6 : ℕ) < 6 at hi
    omega
  · exact Or.inl (by omega)

theorem known_extend (c : Config) (n : ℕ) (old changed : List (Fin 32))
    (a b : SetupState c) (hold : Known c n old a)
    (hf : ScalarFrame c changed a b) (hnew : Known c n changed b) :
    Known c n (old ++ changed) b := by
  intro i hi
  by_cases hm : i ∈ changed
  · exact hnew i hm
  · have hmem : i ∈ old := (List.mem_append.mp hi).resolve_right hm
    exact (congrArg BinaryArithmetic.toNat (hf i hm)).trans (hold i hmem)

theorem known_frame (c : Config) (n : ℕ) (ports : List (Fin 32))
    (a b : SetupState c) (h : Known c n ports a)
    (hf : ∀ i : Fin 32, b.stacks (persistent c i) = a.stacks (persistent c i)) :
    Known c n ports b := by
  intro i hi
  exact (congrArg BinaryArithmetic.toNat (hf i)).trans (h i hi)

def initialKnown : List (Fin 32) := [2, 4, 5]
def finalKnown : List (Fin 32) := [2, 4, 5, 23, 24, 16, 6, 17, 25, 19, 18, 20, 26, 27, 22, 29, 21, 28]

theorem initialKnown_of_words (c : Config) (n : ℕ) (a : SetupState c)
    (hn : BinaryArithmetic.toNat (a.stacks (persistent c 2)) = n)
    (hs : BinaryArithmetic.toNat (a.stacks (persistent c 4)) = SubexpPackingParameters.s n)
    (hu : BinaryArithmetic.toNat (a.stacks (persistent c 5)) = SubexpPackingParameters.u n) :
    Known c n initialKnown a := by
  intro i hi
  simp only [initialKnown, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact hn
  · exact hs
  · exact hu

theorem known_prime (c : Config) (n : ℕ) (ports : List (Fin 32)) (a : SetupState c)
    (h : Known c n ports a) (hi : (6 : Fin 32) ∈ ports) :
    BinaryArithmetic.toNat (a.stacks (persistent c 6)) = SubexpPackingParameters.p n := h 6 hi

theorem known_M (c : Config) (n : ℕ) (ports : List (Fin 32)) (a : SetupState c)
    (h : Known c n ports a) (hi : (23 : Fin 32) ∈ ports) :
    BinaryArithmetic.toNat (a.stacks (persistent c 23)) = DyadicSchedule.M c.T n := h 23 hi

theorem known_B (c : Config) (n : ℕ) (ports : List (Fin 32)) (a : SetupState c)
    (h : Known c n ports a) (hi : (24 : Fin 32) ∈ ports) :
    BinaryArithmetic.toNat (a.stacks (persistent c 24)) = DyadicSchedule.B c.k c.T n := h 24 hi

theorem known_delta (c : Config) (n : ℕ) (ports : List (Fin 32)) (a : SetupState c)
    (h : Known c n ports a) (hi : (16 : Fin 32) ∈ ports) :
    BinaryArithmetic.toNat (a.stacks (persistent c 16)) = DyadicSchedule.delta c.k c.T n := h 16 hi

theorem known_Q (c : Config) (n : ℕ) (ports : List (Fin 32)) (a : SetupState c)
    (h : Known c n ports a) (hi : (17 : Fin 32) ∈ ports) :
    BinaryArithmetic.toNat (a.stacks (persistent c 17)) = DyadicSchedule.Q n := h 17 hi

theorem known_R (c : Config) (n : ℕ) (ports : List (Fin 32)) (a : SetupState c)
    (h : Known c n ports a) (hi : (25 : Fin 32) ∈ ports) :
    BinaryArithmetic.toNat (a.stacks (persistent c 25)) = DyadicSchedule.R c.k c.T n := h 25 hi

theorem known_N (c : Config) (n : ℕ) (ports : List (Fin 32)) (a : SetupState c)
    (h : Known c n ports a) (hi : (18 : Fin 32) ∈ ports) :
    BinaryArithmetic.toNat (a.stacks (persistent c 18)) = DyadicSchedule.N c.k c.T n :=
  (h 18 hi).trans (wanted_blockSize c n)

theorem known_D (c : Config) (n : ℕ) (ports : List (Fin 32)) (a : SetupState c)
    (h : Known c n ports a) (hi : (19 : Fin 32) ∈ ports) :
    BinaryArithmetic.toNat (a.stacks (persistent c 19)) = SubexpPackingParameters.D n := h 19 hi

theorem known_Dstar (c : Config) (n : ℕ) (ports : List (Fin 32)) (a : SetupState c)
    (h : Known c n ports a) (hi : (20 : Fin 32) ∈ ports) :
    BinaryArithmetic.toNat (a.stacks (persistent c 20)) = DyadicSchedule.Dstar c.k c.T n := h 20 hi

theorem known_square (c : Config) (n : ℕ) (ports : List (Fin 32)) (a : SetupState c)
    (h : Known c n ports a) (hi : (26 : Fin 32) ∈ ports) :
    BinaryArithmetic.toNat (a.stacks (persistent c 26)) = DyadicSchedule.R c.k c.T n ^ 2 := h 26 hi

theorem known_tail (c : Config) (n : ℕ) (ports : List (Fin 32)) (a : SetupState c)
    (h : Known c n ports a) (hi : (27 : Fin 32) ∈ ports) :
    BinaryArithmetic.toNat (a.stacks (persistent c 27)) = 16 * DyadicSchedule.Q n * DyadicSchedule.delta c.k c.T n * SubexpPackingParameters.s n := h 27 hi

theorem known_colors (c : Config) (n : ℕ) (ports : List (Fin 32)) (a : SetupState c)
    (h : Known c n ports a) (hi : (21 : Fin 32) ∈ ports) :
    BinaryArithmetic.toNat (a.stacks (persistent c 21)) = SubexpPackingParameters.r n := h 21 hi

theorem known_precision (c : Config) (n : ℕ) (ports : List (Fin 32)) (a : SetupState c)
    (h : Known c n ports a) (hi : (22 : Fin 32) ∈ ports) :
    BinaryArithmetic.toNat (a.stacks (persistent c 22)) = SubexpPackingParameters.D n + 1 := h 22 hi

theorem known_inverseExponent (c : Config) (n : ℕ) (ports : List (Fin 32)) (a : SetupState c)
    (h : Known c n ports a) (hi : (29 : Fin 32) ∈ ports) :
    BinaryArithmetic.toNat (a.stacks (persistent c 29)) = SubexpPackingParameters.p n ^ 4 - 2 := h 29 hi

theorem finalKnown_scalars (c : Config) (n : ℕ) (a : SetupState c)
    (h : Known c n finalKnown a) : ScalarValues c n a := by
  constructor
  · exact known_prime c n finalKnown a h
      (by unfold finalKnown; repeat' first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  · exact known_M c n finalKnown a h
      (by unfold finalKnown; repeat' first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  · exact known_B c n finalKnown a h
      (by unfold finalKnown; repeat' first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  · exact known_delta c n finalKnown a h
      (by unfold finalKnown; repeat' first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  · exact known_Q c n finalKnown a h
      (by unfold finalKnown; repeat' first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  · exact known_R c n finalKnown a h
      (by unfold finalKnown; repeat' first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  · exact known_N c n finalKnown a h
      (by unfold finalKnown; repeat' first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  · exact known_D c n finalKnown a h
      (by unfold finalKnown; repeat' first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  · exact known_Dstar c n finalKnown a h
      (by unfold finalKnown; repeat' first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  · exact known_square c n finalKnown a h
      (by unfold finalKnown; repeat' first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  · exact known_tail c n finalKnown a h
      (by unfold finalKnown; repeat' first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  · exact known_colors c n finalKnown a h
      (by unfold finalKnown; repeat' first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  · exact known_precision c n finalKnown a h
      (by unfold finalKnown; repeat' first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  · exact known_inverseExponent c n finalKnown a h
      (by unfold finalKnown; repeat' first | exact List.mem_cons_self | apply List.mem_cons_of_mem)

end SubexponentialSAT.SubexpSetupProgram

end OAI.Algorithms
