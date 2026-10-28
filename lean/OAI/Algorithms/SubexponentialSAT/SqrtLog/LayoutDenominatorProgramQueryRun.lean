import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQueryCode

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
open SubexpLiftRing SubexpQuarticRing IntegerRingLiftProgram

private theorem staged_outside (a : LocalData) (i : Fin 768) (hi : i∉bank) :
    (staged a).stacks i=a.stacks i := by
  apply copyMany_frame
  intro p hp he
  exact hi (he ▸ pairs_destination p hp)

theorem localCommand_eval (a : LocalData) (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (zero one minusOne : ModelCode t d) (u : RingProgram.ScalarCode 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (hready : CachedReady t model M cache zero one minusOne (localInput a))
    (hu : a.stacks 253=u.val) (hc : ∀i∈bank,a.stacks i=[])
    (hout : a.stacks 728=[]) (W : ℕ) (hw : WordBound W a) (hsize : d*baseWidth 3 t ≤ W) :
    ∃ n ≤ LayoutDenominatorProgram.budget (a.stacks 740).length t d + 589*W+824,
      ∃ out : LocalData, Eval localCommand n a out ∧
        out.stacks=Function.update a.stacks 728 (RingProgram.flat
          (LayoutDenominatorProgram.value t model M cache zero one minusOne u.val (a.stacks 740).length)) := by
  let bits := RingProgram.flat (LayoutDenominatorProgram.value t model M cache
    zero one minusOne u.val (a.stacks 740).length)
  have hs := staged_view a hc
  have hr : CachedReady t model M cache zero one minusOne (view (staged a)).stacks := by
    rw [hs]; exact hready
  have hu' : (view (staged a)).stacks 253=u.val := by rw [hs]; simpa [localInput] using hu
  have h254 : (view (staged a)).stacks 254=[] := by rw [hs]; simp [localInput]
  have h252 : (view (staged a)).stacks 252=[] := by rw [hs]; simp [localInput]
  have hR : (view (staged a)).stacks 239=a.stacks 740 := by rw [hs]; simp [localInput]
  obtain ⟨n,r,hn,he⟩ := LayoutDenominatorProgram.command_run t model M cache hz
    zero one minusOne (view (staged a)).stacks hr u hu' h254 h252 (view (staged a)).regs
  rw [hR] at hn he
  let b : LocalData := embedState id port (staged a)
    (⟨r,Function.update (view (staged a)).stacks 252 bits⟩ : SubexpConvolutionControl.Data)
  have he' : Eval nativeCall (n+1) (staged a) b :=
    eval_liftCommand_from_state _ 239 252 id port (staged a) Function.injective_id port_injective he
  have hbs : b.stacks=Function.update (staged a).stacks 592 bits := by
    change Function.extend port (Function.update (view (staged a)).stacks 252 bits)
      (staged a).stacks = _
    rw [ProgramLinking.extend_update port_injective]
    have hh := congrArg StructuredProgram.State.stacks
      (embedState_project id port (staged a) Function.injective_id port_injective)
    exact congrArg (fun s => Function.update s 592 bits) hh
  have hb728 : b.stacks 728=[] := by
    rw [hbs,Function.update_of_ne (by decide : (728:Fin 768)≠592)]
    exact (staged_outside a 728 (by rw [mem_bank]; decide)).trans hout
  have hb460 : b.stacks 460=[] := by
    rw [hbs,Function.update_of_ne (by decide : (460:Fin 768)≠592)]
    change (view (staged a)).stacks 120=[]
    rw [hs]; simp [localInput]
  have hb592 : b.stacks 592=bits := by rw [hbs]; simp
  let c := copyState 592 728 b
  have hcs : c.stacks=Function.update b.stacks 728 bits := by
    simp only [c,copyState_stack,hb592,hb728,List.append_nil]
  let out := clearManyState bank c
  have hfinal : out.stacks=Function.update a.stacks 728 bits := by
    funext i
    change (clearManyState bank c).stacks i=_
    rw [clearMany_stacks,hcs,hbs]
    by_cases hi : i∈bank
    · rw [ite_eq_left hi]
      have hn : i≠728 := by intro he; subst i; rw [mem_bank] at hi; omega
      rw [Function.update_of_ne hn,hc i hi]
    · rw [ite_eq_right hi]
      by_cases h728 : i=728
      · subst i; simp
      · rw [Function.update_of_ne h728,Function.update_of_ne h728]
        have h592 : i≠592 := by intro he; subst i; exact hi ((mem_bank _).mpr (by omega))
        rw [Function.update_of_ne h592]
        exact staged_outside a i hi
  have hstage : Eval (copyMany 460 pairs) (copyManyCost pairs a) a (staged a) :=
    copyMany_eval _ _ _ pairs_valid (hc 460 ((mem_bank _).mpr (by omega)))
  have hcopy := copy_eval (592:Fin 768) 728 460 b (by decide) (by decide) (by decide) hb460
  have hclear := clearMany_eval bank c
  have hbits : bits.length ≤ W := by
    dsimp [bits]; rw [RingProgram.flat_length]; exact hsize
  have hstageW : WordBound W (staged a) := copyMany_wordBound pairs a W pairs_distinct
    (fun p hp => hc p.2 (pairs_destination p hp)) pairs_separated hw
  have hbW : WordBound W b := by
    intro i; rw [hbs]; by_cases hi : i=592
    · subst i; simp only [Function.update_self]; exact hbits
    · rw [Function.update_of_ne hi]; exact hstageW i
  have hcW : WordBound W c := by
    intro i; rw [hcs]; by_cases hi : i=728
    · subst i; simp only [Function.update_self]; exact hbits
    · rw [Function.update_of_ne hi]; exact hbW i
  have hcost1 := copyManyCost_le pairs a W pairs_separated (fun p _ => hw p.1)
  have hcost3 := clearManyCost_le bank c W hcW
  have hlen : bank.length=256 := by simp [bank]
  simp only [hlen] at hcost3
  have hlenP : pairs.length=10 := rfl
  rw [hlenP] at hcost1
  refine ⟨copyManyCost pairs a+((n+1)+(7*(b.stacks 592).length+5+clearManyCost bank c)),?_,out,?_,hfinal⟩
  · rw [hb592]; omega
  · exact hstage.seq (he'.seq (hcopy.seq hclear))

/-- The ambient wrapper preserves every stack except its persistent output,
and every register outside the local sixteen-register arithmetic bank. -/
theorem command_eval (a : Data) (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (zero one minusOne : ModelCode t d) (u : RingProgram.ScalarCode 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (hready : CachedReady t model M cache zero one minusOne
      (localInput (projectState registers id a)))
    (hu : a.stacks 253=u.val) (hc : ∀i∈bank,a.stacks i=[])
    (hout : a.stacks 728=[]) (W : ℕ) (hw : WordBound W a) (hsize : d*baseWidth 3 t ≤ W) :
    ∃ n ≤ budget (a.stacks 740).length t d W, ∃ out : Data,
      Eval command n a out ∧
      out.stacks=Function.update a.stacks 728 (RingProgram.flat
        (LayoutDenominatorProgram.value t model M cache zero one minusOne u.val (a.stacks 740).length)) ∧
      (∀i : Fin 40,16 ≤ i.val → out.regs i=a.regs i) := by
  obtain ⟨n,hn,b,he,hb⟩ := localCommand_eval (projectState registers id a) t model M cache
    zero one minusOne u hz hready hu hc hout W hw hsize
  refine ⟨n+1,?_,embedState registers id a b,?_,?_,?_⟩
  · unfold budget
    simp only [projectState,Function.comp_apply,id_eq] at hn
    omega
  · exact eval_liftCommand_from_state _ 740 728 registers id a registers_injective Function.injective_id he
  · funext i
    rw [show (embedState registers id a b).stacks i=b.stacks i from
      embedState_stack _ _ _ _ Function.injective_id i]
    exact congrFun hb i
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    dsimp [registers] at hv
    omega

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery

end OAI.Algorithms
