import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgramNative

namespace OAI.Algorithms


/-! Exact unary degree bytes retained from the actual core trace. The
existing native code and all arithmetic services are unchanged. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing StackRoutines
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem coreCommand_eval_degree (a : Data) (bits depth : List Bool) (t : ℕ)
    (ht : 0 < t) (hd : 0 < depth.length)
    (hv : CounterPrograms.value bits=t) (h : CoreInput bits depth a) :
    ∃ n ≤ coreBudget t depth.length bits.length, ∃ e : Data,
      ∃ (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
        (u : RingProgram.ScalarCode 3 t),
      Eval coreCommand n a e ∧
      CoreOutput t depth.length (IrreducibleSearch.data hd) M cache u e ∧
      (∀ i, i∉coreWritePorts → e.stacks i=a.stacks i) ∧
      e.stacks 204=depth := by
  obtain ⟨ns,raw,M,cache,u,lg,hs,ho,hns⟩ := scalarCall_eval a bits t hv ht h.scalarInput
  let a1 := embedState (registers 8 (by decide)) scalar a raw
  have hp (j : Fin 41) : a1.stacks (scalar j)=raw.stacks j :=
    embedState_stack _ _ _ _ scalar_injective j
  have hf (i : Fin 640) (hi : ¬∃ j,scalar j=i) : a1.stacks i=a.stacks i :=
    embedState_stack_frame _ _ _ _ _ hi
  have hm : a1.stacks 194=M.bits := by
    simpa [scalar,IdempotentPreparationProgram.Scalar.low] using
      (hp 5).trans (ho.prepared.rest.1 5)
  have hw : (a1.stacks 202).length=baseWidth 3 t := by
    have hb := ho.unchanged 12 (by decide)
    simpa [scalar,IdempotentPreparationProgram.bootStacks,RingProgram.ternary_baseWidth]
      using congrArg List.length ((hp 12).trans hb)
  have hz : a1.stacks 203=cache.zero.val := (hp 17).trans ho.prepared.zero
  have h1 : a1.stacks 498=cache.one.val := (hp 18).trans ho.prepared.one
  have hm1 : a1.stacks 508=cache.minusOne.val := (hp 28).trans ho.prepared.minusOne
  have hu : a1.stacks 507=u.val := (hp 27).trans ho.prepared.half
  have hprec : a1.stacks 212=List.replicate t true := by
    have hh := (hp 29).trans (ho.unchanged 29 (by decide))
    simpa [scalar,IdempotentPreparationProgram.bootStacks] using hh
  have he253 : a1.stacks 253=[] := (hf 253 (by decide)).trans h.halfEmpty
  have he639 : a1.stacks 639=[] := (hf 639 (by decide)).trans h.copyEmpty
  let a2 : Data := ⟨readRegs a1.regs 30 31 none,Function.update a1.stacks 253 (a1.stacks 507)⟩
  have hcopy : Eval (overwrite 507 253) (7*baseWidth 3 t+8) a1 a2 := by
    simpa [a2,he253,hu,u.property] using overwrite_eval 507 253 a1
      (by decide) (by decide) (by decide) he639
  let a3 := RegisterResetProgram.zeroed a2
  have hreset : Eval RegisterResetProgram.all 32 a2 a3 := RegisterResetProgram.all_eval a2
  have hsearch : projectState (registers 22 (by decide)) search a3 =
      IrreducibleSearchBootstrap.input depth := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      have hdis : ¬∃ i,scalar i=search j := by
        fin_cases j <;> decide
      have hn : search j≠253 := by fin_cases j <;> decide
      simp only [a3,a2,Function.comp_apply,Function.update_of_ne hn]
      rw [hf _ hdis]
      by_cases hj : j=14
      · subst j
        simpa [IrreducibleSearchBootstrap.input,StructuredProgram.ioState,search] using h.degree
      · simpa [IrreducibleSearchBootstrap.input,StructuredProgram.ioState,hj]
          using h.searchClean j hj
  obtain ⟨np,hnp,a4,hpad,hcoeff,hraw,hdepth,hpf⟩ := searchAndPad_eval a3 depth hd t ht
    hsearch (by simpa [a3,a2,RegisterResetProgram.zeroed] using hw)
    (by simpa [a3,a2,RegisterResetProgram.zeroed] using he639)
  have hcarry (i : Fin 640) (hs' : ¬∃ j,search j=i) (hi : i≠253) :
      a4.stacks i=a1.stacks i := by
    rw [hpf i hs']
    simp [a3,a2,hi]
  have hhalf : a4.stacks 253=u.val := by
    rw [hpf 253 (by decide)]
    simp [a3,a2,hu]
  have hseed0 : a4.stacks 538=[] := by
    rw [hcarry 538 (by decide) (by decide),hf 538 (by decide)]
    exact h.tableClean 0 (by decide)
  have hseed1 : a4.stacks 498=cache.one.val :=
    (hcarry 498 (by decide) (by decide)).trans h1
  have hcopy0 : a4.stacks 639=[] :=
    (hcarry 639 (by decide) (by decide)).trans he639
  let a5 : Data := ⟨readRegs a4.regs 30 31 none,Function.update a4.stacks 538 (a4.stacks 498)⟩
  have hload : Eval (overwrite 498 538) (7*baseWidth 3 t+8) a4 a5 := by
    simpa [a5,hseed0,hseed1,cache.one.property] using overwrite_eval 498 538 a4
      (by decide) (by decide) (by decide) hcopy0
  have ti : TableInput t depth.length (IrreducibleSearch.data hd) M cache a5 := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [a5] using (hcarry 194 (by decide) (by decide)).trans hm
    · simpa [a5] using (congrArg List.length (hcarry 202 (by decide) (by decide))).trans hw
    · simp [a5,hdepth]
    · simp [a5,hseed1]
    · simpa [a5] using (hcarry 203 (by decide) (by decide)).trans hz
    · simpa [a5] using (hcarry 508 (by decide) (by decide)).trans hm1
    · change a5.stacks 441 = RingProgramTable.wordBits
        (List.Vector.ofFn (RingProgram.liftCoefficientsRun t
          (IrreducibleSearch.data hd).coefficients).1).val
      rw [RingCoefficientLiftProgram.modelCoefficientBits]
      exact hcoeff
    · intro j hj
      have hj538 : LeafRingSetupProgram.table j≠538 := by
        fin_cases j <;> first | exact (hj (by decide)).elim | decide
      have hj253 : LeafRingSetupProgram.table j≠253 := by fin_cases j <;> decide
      have hd1 : ¬∃ i,search i=LeafRingSetupProgram.table j := by
        fin_cases j <;> first | exact (hj (by decide)).elim | decide
      have hd2 : ¬∃ i,scalar i=LeafRingSetupProgram.table j := by
        fin_cases j <;> first | exact (hj (by decide)).elim | decide
      simp only [a5,Function.update_of_ne hj538]
      rw [hcarry _ hd1 hj253,hf _ hd2]
      exact h.tableClean j (fun hj' => hj (List.mem_cons_of_mem 0 hj'))
  obtain ⟨nt,hnt,e,htable,het,hem,hew,hez,hed,heminus,hef⟩ := tableCall_produces t hd
    (IrreducibleSearch.data hd) M cache ho.prepared.zeroCanonical ho.prepared.oneCanonical a5 ti
  refine ⟨ns+(7*baseWidth 3 t+8)+(32+(np+((7*baseWidth 3 t+8)+nt))),?_,e,M,cache,u,?_,?_,?_,?_⟩
  · unfold coreBudget
    omega
  · simpa only [coreCommand,Nat.add_assoc] using hs.seq (hcopy.seq (hreset.seq (hpad.seq (hload.seq htable))))
  · refine ⟨hem.trans ti.modulus,?_,?_,hez,?_,?_,?_,?_,ho.prepared.inverse,
      ho.prepared.zeroCanonical,ho.prepared.oneCanonical,het⟩
    · exact (congrArg List.length hew).trans ti.width
    · exact (congrArg List.length hed).trans ti.degree
    · rw [hef 498 (by decide)]
      simpa [a5] using hseed1
    · exact heminus
    · rw [hef 253 (by decide)]
      simpa [a5] using hhalf
    · rw [hef 212 (by decide)]
      simpa [a5] using (hcarry 212 (by decide) (by decide)).trans hprec
  · intro i hi
    have hn253 : i≠253 := by
      intro he; subst i; exact hi (by simp [coreWritePorts])
    have hn538 : i≠538 := by
      intro he; subst i; exact hi (by simp [coreWritePorts])
    have hns : ¬∃ j,scalar j=i := by
      rintro ⟨j,rfl⟩; exact hi (by simp [coreWritePorts])
    have hnp : ¬∃ j,search j=i := by
      rintro ⟨j,rfl⟩; exact hi (by simp [coreWritePorts])
    have hnt : ¬∃ j,LeafRingSetupProgram.table j=i := by
      rintro ⟨j,rfl⟩; exact hi (by simp [coreWritePorts])
    rw [hef i hnt]
    change Function.update a4.stacks 538 (a4.stacks 498) i=a.stacks i
    rw [Function.update_of_ne hn538,hcarry i hnp hn253,hf i hns]

  · exact hed.trans (by simpa [a5] using hdepth)

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
