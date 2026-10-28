import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutPrefixStageBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutSizes
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutConstructionBounds

namespace OAI.Algorithms

/-! A fixed polynomial bound for the actual factor/assignment/universal
prefix. The intermediate states are those in the measured stage traces.
Raw clause width is taken from the explicit valid-leaf witness, rather than
inferred from set width when duplicate literals might be present. -/

namespace SubexponentialSAT.SubexpMainLayoutPrefixBounds

open BitProgram StructuredCalls SubexpMainProgram SubexpSetupProgram SubexpPackingParameters
open SubexpMainScheduledLayout SubexpMainLayoutWordBounds Subexp
open SubexpMainLayoutPrefixStageBounds
open scoped BigOperators

local instance scheduledPrime (n : ℕ) : Fact (p n).Prime := ⟨p_prime n⟩

def size (W n k T : ℕ) : ℕ :=
  W + n + k + p n + (p n)^k + r n + ((p n)^4 - 1) + DyadicSchedule.delta k T n +
    MulticolorTypes.blockSize (r n) ((p n)^4 - 1) (DyadicSchedule.delta k T n) + 1

def factorCoefficient : ℕ := 10000 * (50 + 1000000000000 * 7^5) + 1
def assignmentCoefficient : ℕ :=
  SubexpMainLayoutPrefixStageBounds.assignmentCoefficient * (factorCoefficient + 34)^60
def universalCoefficient : ℕ := 2000000 * (factorCoefficient + assignmentCoefficient + 10)^5
def coefficient : ℕ := factorCoefficient + assignmentCoefficient + universalCoefficient + 2

theorem size_pos (W n k T : ℕ) : 1 ≤ size W n k T := by unfold size; omega

private theorem high_relevant {es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) (i : Fin 7) :
    RelevantPort es (SubexpMainLayout.Factors.highPort alloc i) := by
  fin_cases i
  · exact Or.inr ⟨2, rfl, Or.inl (by unfold SubexpMainInvariant.ParameterPort; decide)⟩
  · exact Or.inr ⟨5, rfl, Or.inl (by unfold SubexpMainInvariant.ParameterPort; decide)⟩
  · exact Or.inr ⟨6, rfl, Or.inl (by unfold SubexpMainInvariant.ParameterPort; decide)⟩
  · exact Or.inr ⟨19, rfl, Or.inl (by unfold SubexpMainInvariant.ParameterPort; decide)⟩
  · exact Or.inr ⟨9, rfl, Or.inr (Or.inr rfl)⟩
  · exact master_relevant alloc 0
  · exact master_relevant alloc 1

theorem factor_relevant {es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) (i : Fin 48) :
    RelevantPort es (SubexpMainLayout.Factors.stackMap alloc i) := by
  unfold SubexpMainLayout.Factors.stackMap SubexpMainLayout.Factors.baseMap
  split
  · exact high_relevant alloc _
  · left
    simp only [SubexpLayoutPorts.ordinary]
    have := (SubexpMainLayout.Factors.permutation i).isLt
    omega

private theorem cast_width {n m k : ℕ} (h : n = m) (G : SubexpLeafData.Leaf n)
    (hw : ∀ C ∈ G, C.length ≤ k) :
    ∀ C ∈ SubexpMainLayoutInput.castLeaf h G, C.length ≤ k := by
  cases h
  exact hw

private theorem source_size_arithmetic (X r' Q Δ D k : ℕ) (cs : List (List ℕ))
    (hX : 1 ≤ X) (hr : r' ≤ X) (hQ : Q ≤ X) (hd : Δ ≤ X) (hD : D ≤ X) (hk : k ≤ X)
    (hN : MulticolorTypes.blockSize r' Q Δ ≤ X) (hE : cs.length ≤ Δ * D)
    (hB : (SubexpPlanAlphabetBase.scopeBytes cs).length ≤
      1 + (2 * (1 + (2 * D + 2) * k) + 2) * cs.length) :
    AssignmentFrontendBounds.sourceSize r' Q Δ D cs ≤ 32 * X^4 := by
  have h1 : X ≤ X^4 := AssignmentFrontendBounds.le_power hX (by decide)
  have h2 : X^2 ≤ X^4 := Nat.pow_le_pow_right hX (by decide)
  have h3 : X^3 ≤ X^4 := Nat.pow_le_pow_right hX (by decide)
  have h0 : 1 ≤ X^4 := hX.trans h1
  have he : cs.length ≤ X^2 := hE.trans (by simpa only [pow_two] using Nat.mul_le_mul hd hD)
  have hb : (SubexpPlanAlphabetBase.scopeBytes cs).length ≤ 13 * X^4 := by
    calc
      _ ≤ 1 + (2 * (1 + (2 * X + 2) * X) + 2) * X^2 := hB.trans (by gcongr)
      _ ≤ _ := by ring_nf; omega
  unfold AssignmentFrontendBounds.sourceSize
  omega

private theorem factor_arithmetic (X W F : ℕ) (hX : 1 ≤ X) (hW : W ≤ X^5)
    (hF : F ≤ 1000000000000 * (7 * X)^5) :
    10000 * (48 * W + F + 1) + 1 ≤ factorCoefficient * X^5 := by
  have h1 : 1 ≤ X^5 := Nat.one_le_pow _ _ hX
  rw [mul_pow] at hF
  unfold factorCoefficient
  nlinarith only [h1, hW, hF]

variable {cfg : Config} {er n : ℕ} [NeZero (r n)]
variable {alloc : SubexpLayoutPorts.Allocation (mainExtraStacks cfg)} {hregs : 16 ≤ er}
variable {a : MainState er (mainExtraStacks cfg)} {G : SubexpLeafData.Leaf n}
variable (input : SubexpMainLayoutInput.Ready alloc a n cfg.k cfg.T G)
variable (ready : DyadicSchedule.Ready cfg.k cfg.T n)
variable (actual : Run alloc hregs a G input ready)

omit [NeZero (r n)] in
theorem factor_bound (valid : SubexpMainAssembly.validLeaf cfg n G) (W : ℕ)
    (ha : RelevantWordBound W a) :
    SubexpMainLayout.Factors.runtimeBound alloc a (family input)
      (SubexpMainLayoutInput.castLeaf input.variableCount.symm G) ≤
        factorCoefficient * size W n cfg.k cfg.T ^ 5 := by
  let x := SubexpMainLayout.Factors.sourceInputs alloc a
  let X := size W n cfg.k cfg.T
  have hX : 1 ≤ X := size_pos W n cfg.k cfg.T
  have hW : W ≤ X := by dsimp [X, size]; omega
  have hw5 : W ≤ X^5 := hW.trans (AssignmentFrontendBounds.le_power hX (by decide))
  have hn : SubexpLayoutConstruction.variableCount x = n := input.variableCount
  have hd : SubexpLayoutConstruction.dimension x ≤ n := by
    rw [input.dimension, input.variableCount]
    exact (ChunkPartition.count_le_iff input.ell_pos).mpr (Nat.le_mul_of_pos_right _ input.ell_pos)
  have hmodword := parameter ha 6 (by unfold SubexpMainInvariant.ParameterPort; decide)
  have he : CounterPrograms.value x.counts.ell ≤ W := by
    apply input.width.trans
    simpa only [x, SubexpMainParameterValues.sourceInputs_modulus_word] using hmodword
  have hmass : SubexpLayoutRawPreparation.inputMass x ≤ 5 * W := by
    have h0 := parameter ha 2 (by unfold SubexpMainInvariant.ParameterPort; decide)
    have h1 := parameter ha 5 (by unfold SubexpMainInvariant.ParameterPort; decide)
    have h2 := parameter ha 19 (by unfold SubexpMainInvariant.ParameterPort; decide)
    have h3 := leaf ha
    dsimp only [x, SubexpLayoutRawPreparation.inputMass]
    rw [SubexpMainParameterValues.sourceInputs_n_word,
      SubexpMainParameterValues.sourceInputs_ell_word,
      SubexpMainParameterValues.sourceInputs_modulus_word,
      SubexpMainParameterValues.sourceInputs_dimension_word,
      SubexpMainParameterValues.sourceInputs_leaf]
    omega
  have hs : SubexpLayoutConstructionBounds.sourceSize x (p n) cfg.k ≤ 7 * X := by
    unfold SubexpLayoutConstructionBounds.sourceSize
    rw [hn]
    dsimp only [X, size]
    omega
  have hp : BinaryArithmetic.toNat x.counts.modulus = p n := by
    dsimp only [x]
    rw [SubexpMainParameterValues.sourceInputs_modulus_word]
    simpa only [CounterPrograms.value_eq_toNat] using input.prime
  have hc := SubexpLayoutConstructionBounds.runtimeBound_le x (family input)
    (SubexpMainLayoutInput.castLeaf input.variableCount.symm G) (p n) cfg.k hp
    input.leafBytes (cast_width input.variableCount.symm G valid.2.2.2)
  have hc' : SubexpLayoutConstruction.runtimeBound x (family input)
      (SubexpMainLayoutInput.castLeaf input.variableCount.symm G) ≤
        1000000000000 * (7 * X)^5 := by
    apply hc.trans
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 5)
  have hstored : BitProgram.stackBits ((SubexpMainLayout.Factors.procedure er alloc).project a).stacks ≤
      48 * W := by
    change (∑ i : Fin 48, (a.stacks (SubexpMainLayout.Factors.stackMap alloc i)).length) ≤ _
    exact sum_lengths ha _ (factor_relevant alloc)
  change 10000 * (BitProgram.stackBits _ + SubexpLayoutConstruction.runtimeBound x (family input)
    (SubexpMainLayoutInput.castLeaf input.variableCount.symm G) + 1) + 1 ≤ _
  exact (Nat.add_le_add_right (Nat.mul_le_mul_left 10000
    (Nat.add_le_add_right (Nat.add_le_add_right hstored _) 1)) 1).trans
      (factor_arithmetic X W _ hX hw5 hc')

omit [NeZero (r n)] in
theorem assignment_size_bound (W : ℕ) :
    AssignmentFrontendBounds.sourceSize (r n) ((p n)^4 - 1) (DyadicSchedule.delta cfg.k cfg.T n)
      (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a))
      (scopes input) ≤ 32 * size W n cfg.k cfg.T ^ 4 := by
  let X := size W n cfg.k cfg.T
  have hd : SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a) ≤ n := by
    rw [input.dimension, input.variableCount]
    exact (ChunkPartition.count_le_iff input.ell_pos).mpr (Nat.le_mul_of_pos_right _ input.ell_pos)
  apply source_size_arithmetic X _ _ _ _ cfg.k _ (size_pos W n cfg.k cfg.T)
  · dsimp [X, size]; omega
  · dsimp [X, size]; omega
  · dsimp [X, size]; omega
  · dsimp [X, size]; omega
  · dsimp [X, size]; omega
  · dsimp [X, size]; omega
  · exact SubexpMainLayoutSizes.scope_count input (by have := cfg.width_ge_two; omega)
  · exact SubexpMainLayoutSizes.scope_bytes input (by have := cfg.width_ge_two; omega)

private theorem bound_sum (X F A U : ℕ) (hX : 1 ≤ X)
    (hf : F ≤ factorCoefficient * X^5)
    (ha : A ≤ assignmentCoefficient * X^300)
    (hu : U ≤ universalCoefficient * X^1500) :
    F + A + U + 2 ≤ coefficient * X^1500 := by
  have h5 : X^5 ≤ X^1500 := by
    calc
      X ^ 5 ≤ (X ^ 5) ^ 250 := Nat.le_self_pow (by decide) _
      _ ≤ (X ^ 5) ^ 250 * (X ^ 5) ^ 50 := by
        exact Nat.le_mul_of_pos_right _ (by positivity)
      _ = (X ^ 5) ^ (250 + 50) := (pow_add _ _ _).symm
      _ = X ^ 1500 := by rw [← pow_mul]
  have h300 : X^300 ≤ X^1500 := by
    calc
      X ^ 300 ≤ (X ^ 300) ^ 5 := Nat.le_self_pow (by decide) _
      _ = X ^ 1500 := by rw [← pow_mul]
  have h1 : 1 ≤ X^1500 := (Nat.one_le_pow 5 X hX).trans h5
  have hf' := hf.trans (Nat.mul_le_mul_left factorCoefficient h5)
  have ha' := ha.trans (Nat.mul_le_mul_left assignmentCoefficient h300)
  unfold coefficient
  rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]
  omega

theorem runtimeBound_le (valid : SubexpMainAssembly.validLeaf cfg n G) (W : ℕ)
    (ha : RelevantWordBound W a) :
    SubexpMainLayoutPrefix.runtimeBound alloc a actual.factorState actual.assignmentState
      (family input) (SubexpMainLayoutInput.castLeaf input.variableCount.symm G)
      input.sparse.clause_sets_nodup input.ell_pos (r n) ((p n)^4 - 1)
      (DyadicSchedule.delta cfg.k cfg.T n) ≤ coefficient * size W n cfg.k cfg.T ^ 1500 := by
  let X := size W n cfg.k cfg.T
  let F := SubexpMainLayout.Factors.runtimeBound alloc a (family input)
    (SubexpMainLayoutInput.castLeaf input.variableCount.symm G)
  let S := AssignmentFrontendBounds.sourceSize (r n) ((p n)^4 - 1) (DyadicSchedule.delta cfg.k cfg.T n)
    (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)) (scopes input)
  let A := SubexpMainAssignment.runtimeBound alloc actual.factorState (r n) ((p n)^4 - 1)
    (DyadicSchedule.delta cfg.k cfg.T n)
    (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)) (scopes input)
  let U := SubexpMainUniversalTypes.runtimeBound alloc actual.assignmentState
    (r n) ((p n)^4 - 1) (DyadicSchedule.delta cfg.k cfg.T n)
  have hX : 1 ≤ X := size_pos W n cfg.k cfg.T
  have hW : W ≤ X := by dsimp [X, size]; omega
  have hx5 : X ≤ X^5 := AssignmentFrontendBounds.le_power hX (by decide)
  have h1 : 1 ≤ X^5 := hX.trans hx5
  have h45 : X^4 ≤ X^5 := Nat.pow_le_pow_right hX (by decide)
  have h5300 : X^5 ≤ X^300 := by
    calc
      X ^ 5 ≤ (X ^ 5) ^ 60 := Nat.le_self_pow (by decide) _
      _ = X ^ 300 := by rw [← pow_mul]
  have hx300 : X ≤ X^300 := hx5.trans h5300
  have h1300 : 1 ≤ X^300 := hX.trans hx300
  have hf : F ≤ factorCoefficient * X^5 := factor_bound input valid W ha
  have hs : S ≤ 32 * X^4 := assignment_size_bound input W
  have hb : RelevantWordBound (W + F) actual.factorState :=
    after_run ha actual.stages.choices.factorRun
  have hmeta (i : Fin 4) : CounterPrograms.value
      (actual.factorState.stacks (persistent (mainExtraStacks cfg) (SubexpMainAssignment.metadataIndex i))) =
        (![r n, (p n)^4 - 1, DyadicSchedule.delta cfg.k cfg.T n,
          SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)] : Fin 4 → ℕ) i := by
    obtain ⟨_, hfacts⟩ := actual.stages.choices.factorResult
    rw [SubexpMainLayoutPrefix.factors_persistent_frame hfacts]
    exact input.metadata i
  have ha0 : A ≤ SubexpMainLayoutPrefixStageBounds.assignmentCoefficient * (W + F + S + 1)^60 :=
    assignment_bound alloc actual.factorState (W + F) _ _ _ _ _ hb
      (goodInput_s_pos (DyadicSchedule.ready_goodInput ready)) actual.degree hmeta
  have hdom : W + F + S + 1 ≤ (factorCoefficient + 34) * X^5 := by
    rw [Nat.add_mul]
    have hs' := hs.trans (Nat.mul_le_mul_left 32 h45)
    omega
  have hab : A ≤ assignmentCoefficient * X^300 := by
    calc
      _ ≤ SubexpMainLayoutPrefixStageBounds.assignmentCoefficient *
          ((factorCoefficient + 34) * X^5)^60 :=
        ha0.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hdom 60))
      _ = _ := by rw [mul_pow, ← pow_mul]; simp only [assignmentCoefficient, Nat.mul_assoc]
  have hc : RelevantWordBound (W + F + A) actual.assignmentState :=
    after_run hb actual.stages.choices.assignmentRun
  have hu0 : U ≤ 2000000 * (W + F + A +
      universalSize (r n) ((p n)^4 - 1) (DyadicSchedule.delta cfg.k cfg.T n) + 1)^5 :=
    universal_bound alloc actual.assignmentState (W + F + A) _ _ _ hc
      (goodInput_s_pos (DyadicSchedule.ready_goodInput ready))
  have hus : universalSize (r n) ((p n)^4 - 1) (DyadicSchedule.delta cfg.k cfg.T n) ≤ 5 * X := by
    dsimp [universalSize, X, size]
    omega
  have hud : W + F + A + universalSize (r n) ((p n)^4 - 1)
      (DyadicSchedule.delta cfg.k cfg.T n) + 1 ≤
        (factorCoefficient + assignmentCoefficient + 10) * X^300 := by
    have hf' := hf.trans (Nat.mul_le_mul_left factorCoefficient h5300)
    have hus' := hus.trans (Nat.mul_le_mul_left 5 hx300)
    rw [Nat.add_mul, Nat.add_mul]
    omega
  have hub : U ≤ universalCoefficient * X^1500 := by
    calc
      _ ≤ 2000000 * ((factorCoefficient + assignmentCoefficient + 10) * X^300)^5 :=
        hu0.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hud 5))
      _ = _ := by rw [mul_pow, ← pow_mul]; simp only [universalCoefficient, Nat.mul_assoc]
  have h5To1500 : X^5 ≤ X^1500 := by
    calc
      X ^ 5 ≤ (X ^ 5) ^ 250 := Nat.le_self_pow (by decide) _
      _ ≤ (X ^ 5) ^ 250 * (X ^ 5) ^ 50 := by
        exact Nat.le_mul_of_pos_right _ (by positivity)
      _ = X ^ 1500 := by rw [← pow_add, ← pow_mul]
  have h300To1500 : X^300 ≤ X^1500 := by
    calc
      X ^ 300 ≤ (X ^ 300) ^ 5 := Nat.le_self_pow (by decide) _
      _ = X ^ 1500 := by rw [← pow_mul]
  have h1To1500 : 1 ≤ X^1500 := (Nat.one_le_pow 5 X hX).trans h5To1500
  have hf' := hf.trans (Nat.mul_le_mul_left factorCoefficient h5To1500)
  have hab' := hab.trans (Nat.mul_le_mul_left assignmentCoefficient h300To1500)
  dsimp only [X] at h1To1500 hf' hab' hub
  change F + A + U + 2 ≤ _
  unfold coefficient
  rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]
  omega

theorem start_wordBound (valid : SubexpMainAssembly.validLeaf cfg n G) (W : ℕ)
    (ha : RelevantWordBound W a) :
    RelevantWordBound (W + coefficient * size W n cfg.k cfg.T ^ 1500) actual.start := by
  have h := after_run (after_run (after_run ha actual.stages.choices.factorRun)
    actual.stages.choices.assignmentRun) actual.stages.choices.universalRun
  dsimp only [scopes] at h
  apply mono h
  have hb := runtimeBound_le input ready actual valid W ha
  unfold SubexpMainLayoutPrefix.runtimeBound at hb
  omega

end SubexponentialSAT.SubexpMainLayoutPrefixBounds

end OAI.Algorithms
