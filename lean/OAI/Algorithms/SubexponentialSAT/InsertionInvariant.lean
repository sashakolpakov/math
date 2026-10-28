import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SAT
import OAI.Algorithms.SubexponentialSAT.Sunflower
import OAI.Algorithms.SubexponentialSAT.SunflowerBranch

namespace OAI.Algorithms

/-!
# Degree bounds for live inserted clauses

The state remembers only the still-live clauses inserted on a branch.  Initial
clauses may have arbitrary degree.  A batch inserts at most one clause per
literal, and every inserted clause is shorter than the selected branching width.
A concrete finite trace preserves the degree bound whenever the minimum-width
rule supplies the smaller-width bound for the full parent formula.
-/

namespace SubexponentialSAT.InsertionInvariant

universe u

abbrev Family (α : Type u) := Finset (Finset α)

variable {α : Type u} [DecidableEq α]

/-- Number of clauses of exactly width `j` containing the literal `a`. -/
def widthLiteralDegree (F : Family α) (j : ℕ) (a : α) : ℕ :=
  (F.filter fun C => C.card = j ∧ a ∈ C).card

/-- At most one clause in the batch contains any given literal. -/
def OnePerLiteral (B : Family α) : Prop :=
  ∀ a, (B.filter fun C => a ∈ C).card ≤ 1

/-- The remembered clauses are an actual subfamily of the current formula. -/
structure State (α : Type u) where
  formula : Family α
  tracked : Family α
  tracked_subset : tracked ⊆ formula

/-- Initial clauses are deliberately not marked as inserted. -/
def initial (F : Family α) : State α :=
  ⟨F, ∅, Finset.empty_subset F⟩

/-- Insert a batch and retain exactly the clauses surviving into `G`. -/
def update (s : State α) (B G : Family α) : State α :=
  ⟨G, (s.tracked ∪ B) ∩ G, Finset.inter_subset_right⟩

/-- A batch replacement followed by deletion/absorption. -/
structure BatchStep (s t : State α) where
  selectedWidth : ℕ
  inserted : Family α
  inserted_lt : ∀ C ∈ inserted, C.card < selectedWidth
  onePerLiteral : OnePerLiteral inserted
  child_subset : t.formula ⊆ s.formula ∪ inserted
  tracked_eq : t.tracked = (s.tracked ∪ inserted) ∩ t.formula

/-- The bound supplied before a branch at `d` by choosing minimum width. -/
def PreInsertionBound (L : ℕ → ℕ) (s : State α) (d : ℕ) : Prop :=
  ∀ j, j < d → ∀ a, widthLiteralDegree s.formula j a ≤ L j

/-- Only live inserted clauses, not arbitrary initial clauses, are bounded. -/
def DegreeInvariant (L : ℕ → ℕ) (s : State α) : Prop :=
  ∀ j a, widthLiteralDegree s.tracked j a ≤ L j + 1

theorem widthLiteralDegree_mono {F G : Family α} (h : F ⊆ G) (j : ℕ) (a : α) :
    widthLiteralDegree F j a ≤ widthLiteralDegree G j a := by
  apply Finset.card_le_card
  intro C hC
  exact Finset.mem_filter.mpr ⟨h (Finset.mem_filter.mp hC).1,
    (Finset.mem_filter.mp hC).2⟩

@[simp] theorem widthLiteralDegree_empty (j : ℕ) (a : α) :
    widthLiteralDegree (∅ : Family α) j a = 0 := by
  simp [widthLiteralDegree]

@[simp] theorem widthLiteralDegree_zero (F : Family α) (a : α) :
    widthLiteralDegree F 0 a = 0 := by
  unfold widthLiteralDegree
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro C hC
  obtain ⟨_, hcard, ha⟩ := Finset.mem_filter.mp hC
  have hC : C = ∅ := Finset.card_eq_zero.mp hcard
  simp [hC] at ha

/-- Distinct unit clauses cannot contain the same literal. -/
theorem widthLiteralDegree_one (F : Family α) (a : α) :
    widthLiteralDegree F 1 a ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro C hC D hD
  obtain ⟨_, hcardC, haC⟩ := Finset.mem_filter.mp hC
  obtain ⟨_, hcardD, haD⟩ := Finset.mem_filter.mp hD
  obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp hcardC
  obtain ⟨d, rfl⟩ := Finset.card_eq_one.mp hcardD
  have hc : a = c := Finset.mem_singleton.mp haC
  have hd : a = d := Finset.mem_singleton.mp haD
  rw [← hc, ← hd]

theorem widthLiteralDegree_union_le (F G : Family α) (j : ℕ) (a : α) :
    widthLiteralDegree (F ∪ G) j a ≤
      widthLiteralDegree F j a + widthLiteralDegree G j a := by
  unfold widthLiteralDegree
  rw [Finset.filter_union]
  exact Finset.card_union_le _ _

theorem widthLiteralDegree_le_one_of_onePerLiteral {B : Family α}
    (h : OnePerLiteral B) (j : ℕ) (a : α) : widthLiteralDegree B j a ≤ 1 := by
  apply le_trans _ (h a)
  apply Finset.card_le_card
  intro C hC
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hC).1,
    (Finset.mem_filter.mp hC).2.2⟩

theorem onePerLiteral_singleton (C : Finset α) : OnePerLiteral {C} := by
  intro a
  exact le_trans (Finset.card_filter_le _ _) (by simp)

/-- In child B, disjoint petals give the one-per-literal batch property. -/
theorem onePerLiteral_of_pairwiseDisjoint {B : Family α}
    (h : ∀ C ∈ B, ∀ D ∈ B, C ≠ D → Disjoint C D) : OnePerLiteral B := by
  intro a
  apply Finset.card_le_one.mpr
  intro C hC D hD
  by_contra hne
  obtain ⟨hCB, haC⟩ := Finset.mem_filter.mp hC
  obtain ⟨hDB, haD⟩ := Finset.mem_filter.mp hD
  exact Finset.disjoint_left.mp (h C hCB D hDB hne) haC haD

/-- Deleting clauses can never increase a width-specific literal degree. -/
theorem degreeInvariant_of_tracked_subset {L : ℕ → ℕ} {s t : State α}
    (hsub : t.tracked ⊆ s.tracked) (hs : DegreeInvariant L s) : DegreeInvariant L t := by
  intro j a
  exact (widthLiteralDegree_mono hsub j a).trans (hs j a)

/-- The empty tracked family satisfies the bound even for a dense initial CNF. -/
theorem initial_degreeInvariant (L : ℕ → ℕ) (F : Family α) :
    DegreeInvariant L (initial F) := by
  intro j a
  simp [initial]

/-- No inserted clause has width as large as the selected width. -/
theorem BatchStep.inserted_degree_zero {s t : State α} (e : BatchStep s t)
    {j : ℕ} (h : ¬ j < e.selectedWidth) (a : α) :
    widthLiteralDegree e.inserted j a = 0 := by
  unfold widthLiteralDegree
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro C hC
  obtain ⟨hCB, hcard, _⟩ := Finset.mem_filter.mp hC
  exact h (hcard ▸ e.inserted_lt C hCB)

/-- One actual batch step preserves the insertion degree invariant. -/
theorem BatchStep.preserves_degreeInvariant {L : ℕ → ℕ} {s t : State α}
    (e : BatchStep s t) (hpre : PreInsertionBound L s e.selectedWidth)
    (hs : DegreeInvariant L s) : DegreeInvariant L t := by
  intro j a
  have hsub : t.tracked ⊆ s.tracked ∪ e.inserted := by
    rw [e.tracked_eq]
    exact Finset.inter_subset_left
  have hstart := widthLiteralDegree_mono hsub j a
  have hadd := widthLiteralDegree_union_le s.tracked e.inserted j a
  by_cases hj : j < e.selectedWidth
  · have hold := (widthLiteralDegree_mono s.tracked_subset j a).trans (hpre j hj a)
    have hnew := widthLiteralDegree_le_one_of_onePerLiteral e.onePerLiteral j a
    exact hstart.trans (hadd.trans (Nat.add_le_add hold hnew))
  · have hz := e.inserted_degree_zero hj a
    have hsum : widthLiteralDegree s.tracked j a +
        widthLiteralDegree e.inserted j a ≤ L j + 1 := by
      rw [hz, Nat.add_zero]
      exact hs j a
    exact hstart.trans (hadd.trans hsum)

/-- A finite trace records concrete batches and all intermediate finite states. -/
inductive Trace (L : ℕ → ℕ) : State α → State α → Prop
  | refl (s : State α) : Trace L s s
  | step {s t u : State α} (history : Trace L s t) (event : BatchStep t u)
      (pre : PreInsertionBound L t event.selectedWidth) : Trace L s u

/-- The invariant is propagated by induction over actual branching traces. -/
theorem Trace.preserves_degreeInvariant {L : ℕ → ℕ} {s t : State α}
    (h : Trace L s t) (hs : DegreeInvariant L s) : DegreeInvariant L t := by
  induction h with
  | refl => exact hs
  | step history event pre ih =>
    exact event.preserves_degreeInvariant pre ih

/-- Appendix A.2's degree bound, for every state reachable from an arbitrary CNF. -/
theorem Trace.tracked_degree_le {L : ℕ → ℕ} {F : Family α} {t : State α}
    (h : Trace L (initial F) t) (j : ℕ) (a : α) :
    widthLiteralDegree t.tracked j a ≤ L j + 1 :=
  h.preserves_degreeInvariant (initial_degreeInvariant L F) j a

/-- Filter-form interface for the removal-capacity argument. -/
theorem Trace.tracked_filter_card_le {L : ℕ → ℕ} {F : Family α} {t : State α}
    (h : Trace L (initial F) t) (j : ℕ) (a : α) :
    (t.tracked.filter fun C => C.card = j ∧ a ∈ C).card ≤ L j + 1 :=
  h.tracked_degree_le j a

/-- When every batch member survives absorption, tracking has the usual form. -/
theorem BatchStep.tracked_eq_survivors_union {s t : State α} (e : BatchStep s t)
    (hsurvive : e.inserted ⊆ t.formula) :
    t.tracked = (s.tracked ∩ t.formula) ∪ e.inserted := by
  rw [e.tracked_eq]
  ext C
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hC | hC, ht⟩
    · exact Or.inl ⟨hC, ht⟩
    · exact Or.inr hC
  · rintro (⟨hC, ht⟩ | hC)
    · exact ⟨Or.inl hC, ht⟩
    · exact ⟨Or.inr hC, hsurvive hC⟩

/-- Specialization of the concrete state syntax to the SAT module's literals. -/
abbrev CNFState (V : Type u) := State (SubexponentialSAT.SAT.Literal V)


/-- The paper's `L_j`; at widths zero and one this expression is one. -/
def thresholdDegreeBound (z : ℕ → ℕ) (j : ℕ) : ℕ :=
  (j - 1).factorial * (z j - 1) ^ (j - 1)

@[simp] theorem thresholdDegreeBound_one (z : ℕ → ℕ) :
    thresholdDegreeBound z 1 = 1 := by
  simp [thresholdDegreeBound]

/-- Choosing minimum width excludes the stipulated sunflower at every smaller
width where the branching rule is defined. -/
def MinimumWidth (z : ℕ → ℕ) (F : Family α) (d : ℕ) : Prop :=
  ∀ j, 2 ≤ j → j < d →
    SubexponentialSAT.Sunflower.NonemptyCoreSunflowerFree (F.filter fun C => C.card = j) (z j)

/-- The elementary sunflower theorem discharges the pre-insertion hypothesis.
The zero- and one-width cases use the concrete finite-set facts above. -/
theorem minimumWidth_preInsertionBound {z : ℕ → ℕ}
    (hz : ∀ j, 2 ≤ j → 2 ≤ z j) {s : State α} {d : ℕ}
    (hmin : MinimumWidth z s.formula d) :
    PreInsertionBound (thresholdDegreeBound z) s d := by
  intro j hj a
  by_cases htwo : 2 ≤ j
  · exact SubexponentialSAT.Sunflower.literal_occurrence_le s.formula j (z j)
      (hz j htwo) (hmin j htwo hj) a
  · have hcases : j = 0 ∨ j = 1 := by omega
    rcases hcases with rfl | rfl
    · simp
    · simpa only [thresholdDegreeBound_one] using widthLiteralDegree_one s.formula a

/-- A trace justified by the actual no-smaller-sunflower condition. -/
inductive MinimumWidthTrace (z : ℕ → ℕ) : State α → State α → Prop
  | refl (s : State α) : MinimumWidthTrace z s s
  | step {s t u : State α} (history : MinimumWidthTrace z s t)
      (event : BatchStep t u) (minimum : MinimumWidth z t.formula event.selectedWidth) :
      MinimumWidthTrace z s u

/-- Convert minimum-width combinatorics to the bounds used by the invariant. -/
theorem MinimumWidthTrace.toTrace {z : ℕ → ℕ} {s t : State α}
    (h : MinimumWidthTrace z s t) (hz : ∀ j, 2 ≤ j → 2 ≤ z j) :
    Trace (thresholdDegreeBound z) s t := by
  induction h with
  | refl => exact Trace.refl _
  | step history event minimum ih =>
    exact Trace.step ih event (minimumWidth_preInsertionBound hz minimum)

/-- The invariant with `L_j` derived from the actual sunflower thresholds. -/
theorem MinimumWidthTrace.tracked_degree_le {z : ℕ → ℕ} {F : Family α}
    {t : State α} (h : MinimumWidthTrace z (initial F) t)
    (hz : ∀ j, 2 ≤ j → 2 ≤ z j) (j : ℕ) (a : α) :
    widthLiteralDegree t.tracked j a ≤ thresholdDegreeBound z j + 1 :=
  (h.toTrace hz).tracked_degree_le j a

/-- Direct filter-form statement, for charging a removed tracked clause. -/
theorem MinimumWidthTrace.tracked_filter_card_le {z : ℕ → ℕ} {F : Family α}
    {t : State α} (h : MinimumWidthTrace z (initial F) t)
    (hz : ∀ j, 2 ≤ j → 2 ≤ z j) (j : ℕ) (a : α) :
    (t.tracked.filter fun C => C.card = j ∧ a ∈ C).card ≤
      thresholdDegreeBound z j + 1 :=
  h.tracked_degree_le hz j a


section ConcreteBranches

variable {V : Type u} [DecidableEq V] {d : ℕ}

/-- The state produced by the actual core child, including absorption. -/
def coreChild (s : CNFState V) (flower : SubexponentialSAT.SunflowerBranch.Sunflower V d) :
    CNFState V :=
  update s {flower.core}
    (SubexponentialSAT.SunflowerBranch.childA s.formula flower.core flower.petals)

/-- The state produced by the actual simultaneous-petal child. -/
def petalChild (s : CNFState V) (flower : SubexponentialSAT.SunflowerBranch.Sunflower V d) :
    CNFState V :=
  update s flower.petals
    (SubexponentialSAT.SunflowerBranch.childB s.formula flower.core flower.petals)

/-- The concrete core child satisfies every generic batch-step obligation. -/
def coreBatchStep (s : CNFState V) (flower : SubexponentialSAT.SunflowerBranch.Sunflower V d) :
    BatchStep s (coreChild s flower) where
  selectedWidth := d
  inserted := {flower.core}
  inserted_lt := by
    intro C hC
    have hCeq : C = flower.core := Finset.mem_singleton.mp hC
    rw [hCeq]
    exact flower.core_card_lt
  onePerLiteral := onePerLiteral_singleton flower.core
  child_subset := by
    intro C hC
    change C ∈ SubexponentialSAT.SunflowerBranch.childA s.formula flower.core flower.petals at hC
    have hraw := SubexponentialSAT.SAT.absorb_subset _ hC
    rcases Finset.mem_insert.mp hraw with hcore | hold
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hcore)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hold).1
  tracked_eq := rfl

/-- Disjoint petals meet the batch condition even when all are inserted at once. -/
def petalBatchStep (s : CNFState V) (flower : SubexponentialSAT.SunflowerBranch.Sunflower V d) :
    BatchStep s (petalChild s flower) where
  selectedWidth := d
  inserted := flower.petals
  inserted_lt := by
    intro C hC
    exact flower.petal_card_lt hC
  onePerLiteral := onePerLiteral_of_pairwiseDisjoint flower.pairwise_disjoint
  child_subset := by
    intro C hC
    change C ∈ SubexponentialSAT.SunflowerBranch.childB s.formula flower.core flower.petals at hC
    rcases Finset.mem_union.mp (SubexponentialSAT.SAT.absorb_subset _ hC) with hold | hnew
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hold).1
    · exact Finset.mem_union_right _ hnew
  tracked_eq := rfl

/-- Core insertions survive absorption under the maintained antichain condition. -/
theorem coreChild_tracked (s : CNFState V)
    (flower : SubexponentialSAT.SunflowerBranch.Sunflower V d)
    (hanti : SubexponentialSAT.SunflowerBranch.Antichain s.formula)
    (hpresent : SubexponentialSAT.SunflowerBranch.clauses flower.core flower.petals ⊆ s.formula) :
    (coreChild s flower).tracked =
      (s.tracked ∩ (coreChild s flower).formula) ∪ {flower.core} := by
  apply (coreBatchStep s flower).tracked_eq_survivors_union
  intro C hC
  have hCeq : C = flower.core := Finset.mem_singleton.mp hC
  rw [hCeq]
  exact flower.core_mem_childA hanti hpresent

/-- All petals survive absorption, justifying a batch of their full cardinality. -/
theorem petalChild_tracked (s : CNFState V)
    (flower : SubexponentialSAT.SunflowerBranch.Sunflower V d)
    (hanti : SubexponentialSAT.SunflowerBranch.Antichain s.formula)
    (hpresent : SubexponentialSAT.SunflowerBranch.clauses flower.core flower.petals ⊆ s.formula) :
    (petalChild s flower).tracked =
      (s.tracked ∩ (petalChild s flower).formula) ∪ flower.petals := by
  apply (petalBatchStep s flower).tracked_eq_survivors_union
  exact flower.petals_subset_childB hanti hpresent

/-- An actual branch trace: every chosen sunflower occurs in the parent, has
exactly the prescribed number of petals, and has minimum eligible width. -/
inductive SunflowerTrace (z : ℕ → ℕ) : CNFState V → CNFState V → Prop
  | refl (s : CNFState V) : SunflowerTrace z s s
  | core {s t : CNFState V} {d : ℕ} (history : SunflowerTrace z s t)
      (flower : SubexponentialSAT.SunflowerBranch.Sunflower V d)
      (present : SubexponentialSAT.SunflowerBranch.clauses flower.core flower.petals ⊆ t.formula)
      (size : flower.petals.card = z d)
      (minimum : MinimumWidth z t.formula d) :
      SunflowerTrace z s (coreChild t flower)
  | petals {s t : CNFState V} {d : ℕ} (history : SunflowerTrace z s t)
      (flower : SubexponentialSAT.SunflowerBranch.Sunflower V d)
      (present : SubexponentialSAT.SunflowerBranch.clauses flower.core flower.petals ⊆ t.formula)
      (size : flower.petals.card = z d)
      (minimum : MinimumWidth z t.formula d) :
      SunflowerTrace z s (petalChild t flower)

/-- The generic invariant applies to the literal-set branching algorithm. -/
theorem SunflowerTrace.toMinimumWidthTrace {z : ℕ → ℕ} {s t : CNFState V}
    (h : SunflowerTrace z s t) : MinimumWidthTrace z s t := by
  induction h with
  | refl => exact MinimumWidthTrace.refl _
  | core history flower present size minimum ih =>
    exact MinimumWidthTrace.step ih (coreBatchStep _ flower) minimum
  | petals history flower present size minimum ih =>
    exact MinimumWidthTrace.step ih (petalBatchStep _ flower) minimum

/-- Absorption preserves the antichain convention throughout actual traces. -/
theorem SunflowerTrace.antichain {z : ℕ → ℕ} {s t : CNFState V}
    (h : SunflowerTrace z s t) (hs : SubexponentialSAT.SunflowerBranch.Antichain s.formula) :
    SubexponentialSAT.SunflowerBranch.Antichain t.formula := by
  induction h with
  | refl => exact hs
  | core history flower present size minimum ih =>
    exact SubexponentialSAT.SunflowerBranch.antichain_absorb _
  | petals history flower present size minimum ih =>
    exact SubexponentialSAT.SunflowerBranch.antichain_absorb _

/-- The Appendix A.2 invariant along actual normalized sunflower branches,
without assuming a bound on the initial formula's density. -/
theorem SunflowerTrace.tracked_filter_card_le {z : ℕ → ℕ}
    {F : SubexponentialSAT.SAT.CNF V} {t : CNFState V}
    (h : SunflowerTrace z (initial F) t) (hz : ∀ j, 2 ≤ j → 2 ≤ z j)
    (j : ℕ) (a : SubexponentialSAT.SAT.Literal V) :
    (t.tracked.filter fun C => C.card = j ∧ a ∈ C).card ≤
      thresholdDegreeBound z j + 1 :=
  h.toMinimumWidthTrace.tracked_filter_card_le hz j a

end ConcreteBranches

end SubexponentialSAT.InsertionInvariant

end OAI.Algorithms
