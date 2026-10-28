import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorControlFrames
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorFactorFrames

/-! The conditioned query also excludes the entire retained selector bank.
This accounts for arbitrary incumbent and remaining-round words in the
actual greedy callback's time quantifiers. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorFrames

open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SignatureTupleProgram SignatureTupleNative

local notation "H" => (fun i : Fin 896 => 768 ≤ Fin.val i ∧ Fin.val i ≤ 831)

theorem tuple_port (i : Fin 12) : ¬ H (tupleStacks i) := by
  change ¬ (768 ≤ 836 + i.val ∧ 836 + i.val ≤ 831)
  omega

theorem copy_avoids (src dst tmp : Fin 896)
    (hs : ¬ H src) (hd : ¬ H dst) (ht : ¬ H tmp) :
    AvoidsCmd H (copyWord src dst tmp) :=
  avoids_copyProgram H src dst tmp 0 1 hs hd ht

theorem clear_avoids (src : Fin 896) (hs : ¬ H src) :
    AvoidsCmd H (clearWord src) :=
  avoids_clearProgram H src 0 1 hs

private structure SafeAvoids (c : Cmd 40 896) : Prop where
  proof : AvoidsCmd H c

private theorem SafeAvoids.intro {c : Cmd 40 896} (hc : AvoidsCmd H c) : SafeAvoids c :=
  ⟨hc⟩

private theorem SafeAvoids.seq {first second : Cmd 40 896}
    (hfirst : SafeAvoids first) (hsecond : SafeAvoids second) :
    SafeAvoids (.seq first second) :=
  ⟨⟨hfirst.proof, hsecond.proof⟩⟩

private theorem SafeAvoids.call {l : Nat} {p : Program 40 896 l}
    (hp : AvoidsProgram H p) :
    SafeAvoids (.call p) :=
  ⟨hp⟩

private theorem SafeAvoids.difference (p : DifferencePairsProgram.Ports 40 896)
    {callback : Cmd 40 896} (hc : SafeAvoids callback)
    (hp : ∀ i, ¬ H (p.stack i)) :
    SafeAvoids (DifferencePairsProgram.command p callback) :=
  SafeAvoids.intro
    (QueryElementaryReplay.differenceCommand_avoids H p callback hp hc.proof)

theorem clears_avoids (ports : List (Fin 896))
    (hp : ∀ i ∈ ports, ¬ H i) : AvoidsCmd H (clearWords ports) := by
  induction ports with
  | nil => exact True.intro
  | cons i is ih => exact ⟨clear_avoids i (hp i (by simp)),
      ih (fun j hj => hp j (by simp [hj]))⟩

theorem push_frame_avoids (src dst : Fin 896) (hne : src ≠ dst)
    (hs : ¬ H src) (hd : ¬ H dst) :
    AvoidsCmd H (pushWordCommand src dst hne) := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i
  · exact hs
  · exact hd

theorem pop_frame_avoids (src dst : Fin 896) (hne : src ≠ dst)
    (hs : ¬ H src) (hd : ¬ H dst) :
    AvoidsCmd H (popWordCommand src dst hne) := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i
  · exact hs
  · exact hd

theorem counter_ports_avoid (p : CounterForPrograms.Ports 40 896)
    (hc : ¬ H p.counter) (hs : ¬ H p.scratch) (i : Fin 2) :
    ¬ H (CounterForPrograms.stackPorts p i) := by
  fin_cases i
  · exact hc
  · exact hs

theorem counter_test_avoids (p : CounterForPrograms.Ports 40 896)
    (hc : ¬ H p.counter) (hs : ¬ H p.scratch) :
    AvoidsCmd H (CounterForPrograms.testCmd p) := by
  refine ⟨?_, True.intro⟩
  exact avoids_call_lift_of_range H _ _ _ (counter_ports_avoid p hc hs)

theorem counter_advance_avoids (p : CounterForPrograms.Ports 40 896)
    (hc : ¬ H p.counter) (hs : ¬ H p.scratch) :
    AvoidsCmd H (CounterForPrograms.advanceCmd p) := by
  refine ⟨?_, counter_test_avoids p hc hs⟩
  exact avoids_call_lift_of_range H _ _ _ (counter_ports_avoid p hc hs)

theorem advance_avoids : AvoidsCmd H advanceCommand := by
  refine ⟨?_, counter_advance_avoids remainingPorts (tuple_port 7) (tuple_port 5), True.intro⟩
  exact avoids_call_lift_of_range H _ _ _
    (counter_ports_avoid candidatePorts (tuple_port 2) (tuple_port 10))

theorem fuel_avoids : AvoidsCmd H initialFuelCommand :=
  avoids_call_lift_of_range H _ _ _
    (counter_ports_avoid initialFuelPorts (tuple_port 4) (tuple_port 7))

theorem reset_avoids : AvoidsCmd H resetCommand :=
  ⟨copy_avoids 651 _ _ (by decide) (tuple_port 2) (tuple_port 5),
    copy_avoids 651 _ _ (by decide) (tuple_port 4) (tuple_port 5),
    fuel_avoids, True.intro, True.intro⟩

theorem reset_generator_avoids : AvoidsCmd H resetGeneratorCommand :=
  ⟨reset_avoids, copy_avoids 651 _ _ (by decide) (tuple_port 8) (tuple_port 5)⟩

theorem save_cursor_avoids : AvoidsCmd H saveCursorCommand :=
  ⟨push_frame_avoids _ _ _ (tuple_port 2) (tuple_port 0),
    push_frame_avoids _ _ _ (tuple_port 7) (tuple_port 0)⟩

theorem restore_cursor_avoids : AvoidsCmd H restoreCursorCommand :=
  ⟨pop_frame_avoids _ _ _ (tuple_port 0) (tuple_port 7),
    pop_frame_avoids _ _ _ (tuple_port 0) (tuple_port 2)⟩

theorem record_representative_avoids : AvoidsCmd H recordRepresentativeCommand :=
  ⟨copy_avoids _ _ _ (tuple_port 2) (tuple_port 4) (tuple_port 5),
    push_frame_avoids _ _ _ (tuple_port 4) (tuple_port 1)⟩

theorem descend_level_avoids : AvoidsCmd H descendLevelCommand :=
  ⟨tuple_port 6, True.intro, tuple_port 9, tuple_port 6, True.intro⟩

theorem ascend_level_avoids : AvoidsCmd H ascendLevelCommand :=
  ⟨tuple_port 9, True.intro, tuple_port 6, True.intro⟩

theorem leave_head_avoids : AvoidsCmd H leaveHeadCommand := by
  apply clears_avoids
  intro i hi
  simp only [currentHeadPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> apply tuple_port

theorem drop_representative_avoids : AvoidsCmd H dropRepresentativeCommand :=
  ⟨pop_frame_avoids _ _ _ (tuple_port 1) (tuple_port 4), clear_avoids _ (tuple_port 4)⟩

theorem test_parent_avoids : AvoidsCmd H testParentCommand := tuple_port 0

theorem test_available_avoids : AvoidsCmd H testAvailableCommand :=
  ⟨counter_test_avoids remainingPorts (tuple_port 7) (tuple_port 5), True.intro⟩

theorem initialize_levels_avoids : AvoidsCmd H initializeLevelsCommand :=
  ⟨copy_avoids 130 _ _ (by decide) (tuple_port 6) (tuple_port 5),
    copy_avoids 649 _ _ (by decide) (tuple_port 9) (tuple_port 5),
    tuple_port 6, True.intro, True.intro⟩

theorem initialize_fresh_avoids : AvoidsCmd H initializeFreshCommand :=
  ⟨clear_avoids _ (by decide), True.intro, show ¬ H (rescanStacks 22) from by decide⟩

theorem advance_candidate_avoids : AvoidsCmd H advanceCandidateCommand :=
  ⟨advance_avoids, clear_avoids _ (tuple_port 3)⟩

theorem reset_predecessor_avoids : AvoidsCmd H resetPredecessorCommand :=
  copy_avoids 651 _ _ (by decide) (tuple_port 8) (tuple_port 5)

theorem probe_avoids (predicate : Cmd 40 896) (hp : AvoidsCmd H predicate) :
    AvoidsCmd H (probeWith predicate) :=
  ⟨test_available_avoids, ⟨initialize_fresh_avoids, hp,
    show ¬ H (rescanStacks 22) from by decide⟩, True.intro⟩

theorem descend_avoids (loadHead : Cmd 40 896) (hl : AvoidsCmd H loadHead) :
    AvoidsCmd H (descendWith loadHead) :=
  ⟨record_representative_avoids, save_cursor_avoids, descend_level_avoids,
    leave_head_avoids, True.intro, hl, reset_generator_avoids⟩

theorem resume_parent_avoids (loadHead : Cmd 40 896) (hl : AvoidsCmd H loadHead) :
    AvoidsCmd H (resumeParentWith loadHead) :=
  ⟨drop_representative_avoids, restore_cursor_avoids, ascend_level_avoids,
    hl, reset_predecessor_avoids, advance_candidate_avoids⟩

theorem ascend_avoids (loadHead : Cmd 40 896) (hl : AvoidsCmd H loadHead) :
    AvoidsCmd H (ascendWith loadHead) :=
  ⟨leave_head_avoids, test_parent_avoids, resume_parent_avoids loadHead hl, True.intro⟩

theorem setup_avoids (loadHead : Cmd 40 896) (hl : AvoidsCmd H loadHead) :
    AvoidsCmd H (setupWith loadHead) := by
  refine ⟨?_, initialize_levels_avoids, True.intro, hl, reset_generator_avoids⟩
  apply clears_avoids
  intro i hi
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
  exact tuple_port j

/-- This covers the actual fixed attained-signature DFS, including all
presence tests, cursor scans and frame manipulation. -/
theorem tuple_controller_avoids (loadHead predicate visit : Cmd 40 896)
    (hl : AvoidsCmd H loadHead) (hp : AvoidsCmd H predicate)
    (hv : AvoidsCmd H visit) :
    AvoidsCmd H (SignatureTupleProgram.command controllerPorts
      (assembleRoutines loadHead predicate visit)) :=
  ⟨setup_avoids loadHead hl, ⟨hv, ascend_avoids loadHead hl⟩,
    probe_avoids predicate hp,
    ⟨descend_avoids loadHead hl, advance_candidate_avoids⟩,
    ascend_avoids loadHead hl⟩

private theorem SafeAvoids.tupleController
    {loadHead predicate visit : Cmd 40 896}
    (hl : SafeAvoids loadHead) (hp : SafeAvoids predicate)
    (hv : SafeAvoids visit) :
    SafeAvoids (SignatureTupleProgram.command controllerPorts
      (assembleRoutines loadHead predicate visit)) :=
  SafeAvoids.intro
    (tuple_controller_avoids loadHead predicate visit hl.proof hp.proof hv.proof)

theorem candidate_avoids : AvoidsCmd H candidateCall := by
  apply avoids_call_lift_of_range
  intro i
  change ¬ (768 ≤ (if i.val = 0 then 141 else if i.val = 15 then 847 else
    if i.val = 16 then 838 else if i.val = 17 then 839 else
    if i.val = 18 then 844 else 340 + i.val) ∧
    (if i.val = 0 then 141 else if i.val = 15 then 847 else
      if i.val = 16 then 838 else if i.val = 17 then 839 else
      if i.val = 18 then 844 else 340 + i.val) ≤ 831)
  split_ifs <;> omega

theorem overwrite_avoids (src dst : Fin 896) (hs : ¬ H src) (hd : ¬ H dst) :
    AvoidsCmd H (QueryTupleVisitor.overwrite src dst) :=
  ⟨avoids_clearProgram H dst 0 1 hd, copy_avoids src dst 841 hs hd (by decide)⟩

theorem replay_avoids (work : Cmd 40 896) (hw : AvoidsCmd H work) :
    AvoidsCmd H (QueryExecution.replay work) :=
  ⟨⟨overwrite_avoids 837 840 (by decide) (by decide),
    overwrite_avoids 845 843 (by decide) (by decide)⟩,
    show ¬ H 840 from by decide,
    ⟨pop_frame_avoids 840 838 (by decide) (by decide) (by decide),
      show ¬ H 843 from by decide⟩,
    hw, avoids_clearProgram H 838 0 1 (by decide), show ¬ H 840 from by decide⟩

private theorem SafeAvoids.replay {work : Cmd 40 896} (hw : SafeAvoids work) :
    SafeAvoids (QueryExecution.replay work) :=
  SafeAvoids.intro (replay_avoids work hw.proof)

theorem environment_avoids : AvoidsCmd H FactorEnvironment.bootstrap := by
  apply avoids_liftProgram
  apply avoids_compiled
  apply avoids_copyMany
  · decide
  · simp [FactorEnvironment.pairs, Fin.coe_ofNat_eq_mod]

theorem clear_pair_avoids : AvoidsCmd H QueryAssembler.clearPair := by
  apply avoids_liftProgram
  apply avoids_compiled
  apply avoids_clearMany
  intro i hi
  have hh := (QueryAssembler.pairScratch_mem i).mp hi
  rcases hh with hh | hh | rfl | rfl | rfl | rfl
  · change ¬ H i
    omega
  · change ¬ H i
    omega
  all_goals decide

theorem pair_sign_avoids : AvoidsCmd H QueryProgram.pairSignCall := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i <;> decide

theorem signed_accumulate_avoids : AvoidsCmd H QueryProgram.signedAccumulate := by
  constructor
  · apply avoids_call_lift_of_range
    intro i
    change ¬ H (QueryProgram.leafScalePorts i)
    simp only [QueryProgram.leafScalePorts]
    split_ifs <;> simp only [Fin.coe_ofNat_eq_mod] <;> have hi := i.isLt <;> omega
  · apply avoids_call_lift_of_range
    intro i
    change ¬ H (QueryProgram.leafNormalizePorts i)
    simp only [QueryProgram.leafNormalizePorts]
    split_ifs <;> simp only [Fin.coe_ofNat_eq_mod] <;> have hi := i.isLt <;> omega

theorem pair_update_avoids : AvoidsCmd H QueryProgram.pairUpdate :=
  ⟨pair_sign_avoids, signed_accumulate_avoids, show ¬ H 848 from by decide⟩

theorem commit_pair_avoids : AvoidsCmd H QueryAssembler.commitPair :=
  ⟨⟨clear_pair_avoids, environment_avoids,
    overwrite_avoids 211 34 (by decide) (by decide)⟩,
    pair_update_avoids, clear_pair_avoids⟩


theorem tuple_clear_bank_avoids (ports : List (Fin 896))
    (hp : ∀ i ∈ ports, ¬ H i) : AvoidsCmd H (QueryTupleInit.clearBank ports) := by
  apply avoids_liftProgram
  apply avoids_compiled
  exact avoids_clearMany H ports hp

theorem factor_move_avoids (K : Fin 768 → Prop) (src dst : Fin 768)
    (hs : ¬ K src) (hd : ¬ K dst) (ht : ¬ K 159) :
    AvoidsCmd K (SqrtLog.LeafProgram.Factor.move src dst) :=
  ⟨avoids_copyProgram K src dst 159 0 1 hs hd ht,
    avoids_clearProgram K src 0 1 hs⟩

theorem tuple_multiply_call_avoids : AvoidsCmd H QueryAssembler.TupleMultiply.multiply := by
  apply avoids_liftProgram
  apply avoids_compiled
  refine ⟨factor_move_avoids _ 67 61 (by decide) (by decide) (by decide),
    factor_move_avoids _ 151 67 (by decide) (by decide) (by decide), ?_,
    factor_move_avoids _ 67 151 (by decide) (by decide) (by decide)⟩
  apply avoids_call_lift_of_range
  intro i
  change ¬ H (QueryAssembler.TupleMultiply.ports (SqrtLog.LeafProgram.Factor.nativeStacks i))
  simp only [QueryAssembler.TupleMultiply.ports]
  split_ifs
  · decide
  · decide
  · change ¬ (768 ≤ i.val ∧ i.val ≤ 831)
    have hi := i.isLt
    omega

theorem tuple_multiply_avoids : AvoidsCmd H QueryAssembler.TupleMultiply.command := by
  refine ⟨⟨NodeFinishReplay.clearMany_avoids H [61,70] ?_,
    clear_pair_avoids, environment_avoids⟩,
    tuple_multiply_call_avoids, clear_pair_avoids⟩
  intro i hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl <;> decide


private theorem instr_five {r s l : ℕ} (c : Instr r s l)
    (hc : AvoidsInstr (fun i : Fin s => i.val=320 ∨ i.val=322) c)
    (hs : AvoidsInstr (fun i : Fin s => 768 ≤ i.val ∧ i.val ≤ 831) c) :
    AvoidsInstr (fun i : Fin s => i.val=320 ∨ i.val=322 ∨ i.val=770 ∨ i.val=771 ∨ i.val=781) c := by
  cases c <;> simp only [AvoidsInstr] at * <;>
    first | exact True.intro | omega

private theorem base_five {r s : ℕ} (c : StructuredProgram.Cmd r s)
    (hc : AvoidsBase (fun i : Fin s => i.val=320 ∨ i.val=322) c)
    (hs : AvoidsBase (fun i : Fin s => 768 ≤ i.val ∧ i.val ≤ 831) c) :
    AvoidsBase (fun i : Fin s => i.val=320 ∨ i.val=322 ∨ i.val=770 ∨ i.val=771 ∨ i.val=781) c := by
  induction c with
  | skip => exact True.intro
  | atom a =>
    cases a <;> simp only [AvoidsBase, AvoidsAtom] at * <;>
      first | exact True.intro | omega
  | seq a b ha hb => exact ⟨ha hc.1 hs.1, hb hc.2 hs.2⟩
  | ite i a b ha hb => exact ⟨ha hc.1 hs.1, hb hc.2 hs.2⟩
  | «while» i a ha => exact ha hc hs

private theorem command_five {r s : ℕ} (c : Cmd r s)
    (hc : AvoidsCmd (fun i : Fin s => i.val=320 ∨ i.val=322) c)
    (hs : AvoidsCmd (fun i : Fin s => 768 ≤ i.val ∧ i.val ≤ 831) c) :
    AvoidsCmd (fun i : Fin s => i.val=320 ∨ i.val=322 ∨ i.val=770 ∨ i.val=771 ∨ i.val=781) c := by
  induction c with
  | base a => exact base_five a hc hs
  | call p => exact fun q => instr_five (p.code q) (hc q) (hs q)
  | seq a b ha hb => exact ⟨ha hc.1 hs.1, hb hc.2 hs.2⟩
  | ite i a b ha hb => exact ⟨ha hc.1 hs.1, hb hc.2 hs.2⟩
  | «while» i a ha => exact ha hc hs

open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

private theorem loader_clearMany_avoids (ps : List (Fin 896))
    (hp : ∀ p ∈ ps, ¬ (768 ≤ p.val ∧ p.val ≤ 831)) :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val ≤ 831) (clearMany ps) := by
  induction ps with
  | nil => exact True.intro
  | cons p ps ih =>
    exact ⟨avoids_clearProgram _ p 0 1 (hp p (by simp)),
      ih (fun q hq => hp q (by simp [hq]))⟩

theorem lower_avoids {r l : ℕ} (p : Program r 768 l) (reg : Fin r → Fin 40) :
    AvoidsProgram (fun i : Fin 896 => 768 ≤ i.val ∧ i.val ≤ 831)
      (ProgramLinking.liftProgram p reg SignatureHeadLoader.lowStacks) := by
  apply avoids_liftProgram_of_range
  intro i hi
  have hv := i.isLt
  change 768 ≤ i.val ∧ i.val ≤ 831 at hi
  omega

theorem programFrom_avoids (src : Fin 896) (hs : ¬ (768 ≤ src.val ∧ src.val ≤ 831)) :
    AvoidsProgram (fun i : Fin 896 => 768 ≤ i.val ∧ i.val ≤ 831)
      (SignatureHeadLoader.programFrom src) := by
  apply avoids_liftProgram
  apply avoids_compiled
  refine ⟨⟨?_,?_⟩,?_,?_,?_,?_⟩
  · exact loader_clearMany_avoids [649,659,846,847] (by norm_num [Fin.coe_ofNat_eq_mod])
  · exact avoids_copyProgram _ src 649 659 0 1 hs (by decide) (by decide)
  · apply avoids_liftProgram_of_range
    intro i hi
    have hv := i.isLt
    change 768 ≤ i.val ∧ i.val ≤ 831 at hi
    omega
  · exact avoids_clearProgram _ 659 0 1 (by decide)
  · exact avoids_copyProgram _ 668 847 659 0 1 (by decide) (by decide) (by decide)
  · exact loader_clearMany_avoids [668,669,846] (by norm_num [Fin.coe_ofNat_eq_mod])

theorem program843_avoids :
    AvoidsProgram (fun i : Fin 896 => 768 ≤ i.val ∧ i.val ≤ 831)
      (SignatureHeadLoader.programFrom 843) := programFrom_avoids 843 (by decide)

theorem program845_avoids :
    AvoidsProgram (fun i : Fin 896 => 768 ≤ i.val ∧ i.val ≤ 831)
      (SignatureHeadLoader.programFrom 845) := programFrom_avoids 845 (by decide)


private theorem interval_convert {c : Cmd 40 896}
    (h : AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832) c) :
    AvoidsCmd H c := by simpa only [Nat.lt_succ_iff] using h

theorem tuple_sum_avoids : AvoidsCmd H QueryTupleSum.command := by
  refine ⟨⟨interval_convert QuerySelectorControlFrames.nodeAppendPrepare_avoids,
    NodeFinishReplay.clearMany_avoids H _ ?_⟩, ?_⟩
  · intro i hi
    have hh := QueryTupleSum.scratchPorts_low hi
    omega
  · apply avoids_call_lift_of_range
    intro i
    change ¬ H (QueryTupleSum.ports i)
    simp only [QueryTupleSum.ports]
    split_ifs <;> simp only [Fin.coe_ofNat_eq_mod] <;> have hi := i.isLt <;> omega

theorem tuple_end_avoids : AvoidsCmd H QueryExecution.TupleEnd.command := by
  refine ⟨tuple_sum_avoids, tuple_clear_bank_avoids _ ?_⟩
  intro i hi
  simp only [currentHeadPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> apply tuple_port

theorem pair_start_avoids : AvoidsCmd H QueryExecution.PairStart.command :=
  ⟨clear_avoids 851 (by decide), interval_convert QuerySelectorControlFrames.expandCaller_avoids⟩

theorem representative_install_avoids : AvoidsCmd H QueryTupleVisitor.installRepresentative :=
  ⟨overwrite_avoids 838 859 (by decide) (by decide),
    avoids_compiled H _ (interval_convert QuerySelectorFactorFrames.Head.overlay_avoids) _ _,
    overwrite_avoids 145 869 (by decide) (by decide),
    avoids_clearProgram H 859 0 1 (by decide)⟩

theorem tuple_init_avoids
    (hsetup : AvoidsCmd H FactorAssignmentProgram.setup) :
    AvoidsCmd H QueryTupleInit.command := by
  have hlo : ∀ i ∈ QueryTupleInit.lowPorts, ¬ H i := by
    intro i hi
    have hh := (QueryTupleInit.mem_lowPorts i).mp hi
    omega
  refine ⟨tuple_clear_bank_avoids _ ?_, hsetup,
    overwrite_avoids 69 852 (by decide) (by decide),
    overwrite_avoids 703 869 (by decide) (by decide),
    tuple_clear_bank_avoids _ hlo⟩
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact hlo i hi
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    subst i
    decide


theorem head_sum_avoids : AvoidsCmd H (HeadSumAssembly.head HeadSumAssembly.accepted) :=
  interval_convert QuerySelectorFactorFrames.head_avoids

theorem concrete_tuple_init_avoids : AvoidsCmd H QueryTupleInit.command :=
  tuple_init_avoids (interval_convert QuerySelectorFactorFrames.setup_avoids)

theorem head_prepare_avoids : AvoidsCmd H SignatureHeadPrepare.command :=
  interval_convert QuerySelectorFactorFrames.Prepare.command_avoids

/-- The fixed visitor composes the actual two passes and all arithmetic
without any access to the suspended outer collector. -/
theorem visitor_avoids_of_loader
    (hload : AvoidsProgram H (SignatureHeadLoader.programFrom 843)) :
    AvoidsCmd H QueryVisitorProgram.visitor := by
  have hload' := SafeAvoids.call hload
  have hbaselineSafe := hload'.seq (SafeAvoids.intro representative_install_avoids)
  have hbaseline : AvoidsCmd H QueryVisitorProgram.baselineHead := by
    have hpack : ∃ c, c=QueryVisitorProgram.baselineHead ∧ SafeAvoids c := by
      refine ⟨_,?_,hbaselineSafe⟩
      rw [QueryVisitorProgram.baselineHead]
    obtain ⟨_,rfl,hc⟩ := hpack
    exact hc.proof
  have hevaluateSafe := hload'.seq ((SafeAvoids.intro head_prepare_avoids).seq
    ((SafeAvoids.intro head_sum_avoids).seq (SafeAvoids.intro tuple_multiply_avoids)))
  have hevaluate : AvoidsCmd H QueryVisitorProgram.evaluateHead := by
    have hpack : ∃ c, c=QueryVisitorProgram.evaluateHead ∧ SafeAvoids c := by
      refine ⟨_,?_,hevaluateSafe⟩
      rw [QueryVisitorProgram.evaluateHead,QueryVisitorProgram.loadHead,
        QueryVisitorProgram.evaluateLoadedHead]
    obtain ⟨_,rfl,hc⟩ := hpack
    exact hc.proof
  have hvisitor := (SafeAvoids.intro concrete_tuple_init_avoids).seq
    ((SafeAvoids.intro hbaseline).replay.seq
      ((SafeAvoids.intro hevaluate).replay.seq (SafeAvoids.intro tuple_end_avoids)))
  have hpack : ∃ c, c=QueryVisitorProgram.visitor ∧ SafeAvoids c := by
    refine ⟨_,?_,hvisitor⟩
    rw [QueryVisitorProgram.visitor]
  obtain ⟨_,rfl,hc⟩ := hpack
  exact hc.proof

theorem tuple_avoids_of_loader
    (hload : AvoidsProgram H (SignatureHeadLoader.programFrom 845))
    (hvisit : AvoidsCmd H QueryVisitorProgram.visitor) :
    AvoidsCmd H SignatureTupleComplete.command := by
  have htuple := (SafeAvoids.call hload).tupleController
    (SafeAvoids.intro candidate_avoids) (SafeAvoids.intro hvisit)
  have hpack : ∃ c, c=SignatureTupleComplete.command ∧ SafeAvoids c := by
    refine ⟨_,?_,htuple⟩
    rw [SignatureTupleComplete.command,SignatureTupleComplete.routines,
      SignatureTupleLoader.loadHead,SignatureTupleLoader.headAddress]
  obtain ⟨_,rfl,hc⟩ := hpack
  exact hc.proof

theorem visitor_avoids : AvoidsCmd H QueryVisitorProgram.visitor :=
  visitor_avoids_of_loader program843_avoids

theorem tuple_avoids : AvoidsCmd H SignatureTupleComplete.command :=
  tuple_avoids_of_loader program845_avoids visitor_avoids

private theorem tuple_safe : SafeAvoids SignatureTupleComplete.command :=
  ⟨tuple_avoids⟩

private theorem pairCallback_safe : SafeAvoids QueryStreamProgram.pairCallback := by
  let hs := (SafeAvoids.intro (c := QueryExecution.PairStart.command)
      pair_start_avoids).seq
    (tuple_safe.seq (SafeAvoids.intro (c := QueryAssembler.commitPair)
      commit_pair_avoids))
  have hpack : ∃ c, c = QueryStreamProgram.pairCallback ∧ SafeAvoids c := by
    refine ⟨_, ?_, hs⟩
    rw [QueryStreamProgram.pairCallback]
  obtain ⟨_, rfl, hc⟩ := hpack
  exact hc

private theorem pairs_safe : SafeAvoids QueryStreamProgram.pairs := by
  have hp : ∀ i, ¬ H (QueryStreamProgram.pairPorts.stack i) := by
    intro i
    change ¬ (768 ≤ 832 + i.val ∧ 832 + i.val ≤ 831)
    omega
  let hs := pairCallback_safe.difference QueryStreamProgram.pairPorts hp
  have hpack : ∃ c, c = QueryStreamProgram.pairs ∧ SafeAvoids c := by
    refine ⟨_, ?_, hs⟩
    rw [QueryStreamProgram.pairs]
  obtain ⟨_, rfl, hc⟩ := hpack
  exact hc

theorem pairs_avoids : AvoidsCmd H QueryStreamProgram.pairs := pairs_safe.proof


theorem bootstrap_avoids : AvoidsCmd H QueryStreamProgram.bootstrapNode :=
  lower_avoids SignatureHeadLoader.bootstrapProgram SignatureHeadLoader.leafRegs

theorem node_body_avoids : AvoidsCmd H QueryStreamProgram.nodeBody :=
  ⟨interval_convert QuerySelectorControlFrames.beginNode_avoids,
    interval_convert QuerySelectorControlFrames.nativeLayoutLoad_avoids, bootstrap_avoids,
    interval_convert QuerySelectorControlFrames.setupCaller_avoids, pairs_avoids,
    interval_convert QuerySelectorControlFrames.nodeFinish_avoids⟩

theorem nodes_avoids : AvoidsCmd H QueryStreamProgram.nodes := by
  refine ⟨interval_convert QuerySelectorControlFrames.initializeNodes_avoids, ?_, node_body_avoids⟩
  change ¬ H 301
  decide

/-- The actual fixed conditioned query excludes the whole retained selector
bank, including every invoked table and every peek. -/
theorem command_avoids : AvoidsCmd H QueryStreamProgram.command :=
  ⟨interval_convert QuerySelectorControlFrames.prepareHigh_avoids, nodes_avoids,
    interval_convert QuerySelectorControlFrames.reconstruction_avoids⟩

theorem program_avoids : AvoidsProgram H QueryStreamProgram.program :=
  avoids_compiled H _ command_avoids 330 323

local notation "K" => (fun i : Fin 896 => Fin.val i=320 ∨ Fin.val i=322 ∨
  Fin.val i=770 ∨ Fin.val i=771 ∨ Fin.val i=781)

/-- All five unconstrained words in the concrete greedy query-time binder
are excluded from the fixed conditioned query's actual instruction stream. -/
theorem five_word_command_avoids : AvoidsCmd K QueryStreamProgram.command :=
  command_five _ QueryStreamFrames.command_avoids command_avoids

theorem five_word_program_avoids : AvoidsProgram K QueryStreamProgram.program :=
  avoids_compiled K _ five_word_command_avoids 330 323

theorem shadow_eval {steps : ℕ} {a b : State 40 896}
    (he : Eval QueryStreamProgram.command steps (rebaseState K (fun _ => []) a) b) :
    Eval QueryStreamProgram.command steps a (rebaseState K a.stacks b) :=
  CommandStackTransport.eval_shadow K five_word_command_avoids he

theorem shadow_prefix_bound {steps localBound frameBound : ℕ} {a b : State 40 896}
    (he : Eval QueryStreamProgram.command steps (rebaseState K (fun _ => []) a) b)
    (hlocal : ∀ prefixSteps source, prefixSteps ≤ steps+1 →
      Trace QueryStreamProgram.program prefixSteps
        ((rebaseState K (fun _ => []) a).withPC (some QueryStreamProgram.program.entry)) source →
      ∀ i, ¬ K i → (source.stacks i).length ≤ localBound)
    (hframe : ∀ i, K i → (a.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps+1 →
      Trace QueryStreamProgram.program prefixSteps
        (a.withPC (some QueryStreamProgram.program.entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max localBound frameBound :=
  CommandStackTransport.eval_shadow_prefix_bound K five_word_command_avoids 330 323 he hlocal hframe

theorem shadow_count_word (a b : State 40 896) :
    (rebaseState K a.stacks b).stacks 323=b.stacks 323 := rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorFrames
