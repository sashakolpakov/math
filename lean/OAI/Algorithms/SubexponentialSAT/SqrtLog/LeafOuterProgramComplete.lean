import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramJoin
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramInitialResource
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramMainState

namespace OAI.Algorithms

/-! Actual whole-leaf traces from the remaining two native services.  The
supplier is restricted to states reached by the fixed initial-code program;
it is not an instruction or a semantic evaluation oracle. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage Filter
open scoped Topology

abbrev NativeSupply {n : ℕ} (F : ExecCNF.Formula (SAT.Literal (Fin n))) (B : ℕ)
    (mass acceptedCount : Cmd 40 896) (a : Data) (limit : ℕ) : Prop :=
  ∀ ni p (s : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B),
    Eval initialCode ni (classified a (formulaRecords F)) p →
    StartReady p n F.length B →
    WalshExistence.Good (SparseCode.gapDenom F.length B) s →
    SparseCode.HasDistance Q (SparseCode.degree F.length B/(100*B*SparseCode.logSize F.length)+1) →
    p.stacks 777=HashSelectProgram.candidateEncoding
      (LeafScopeResourceBounds.initialPayloads (p.stacks 768).length
        (CodeRowsProgram.serializedRows F.length s Q)) →
    (∀ i : Fin 896, 784 ≤ i.val → i.val < 800 → p.stacks i=a.stacks i) →
    ∃ svc : NativeServices (formulaClauses F) mass acceptedCount p
      (LeafScopeResourceBounds.initialPayloads (p.stacks 768).length
        (CodeRowsProgram.serializedRows F.length s Q)), svc.budget ≤ limit

theorem coreInput_wordBound {a : Data} {bits nw Bw : List Bool}
    (h : MainAdapter.CoreInput a bits nw Bw) :
    WordBound (bits.length+nw.length+Bw.length+1) a := by
  intro i
  rw [h i]
  split_ifs <;> (try simp only [List.length_nil]) <;> omega

theorem coreInput_empty {a : Data} {bits nw Bw : List Bool}
    (h : MainAdapter.CoreInput a bits nw Bw) (i : Fin 896) (hi : i.val ≤ 782) :
    a.stacks i=[] := by
  have h784 : i≠784 := by intro he; have := congrArg Fin.val he; omega
  have h785 : i≠785 := by intro he; have := congrArg Fin.val he; omega
  have h786 : i≠786 := by intro he; have := congrArg Fin.val he; omega
  simp only [h i,ite_eq_right h784,ite_eq_right h785,ite_eq_right h786]

theorem coreInput_classifier {a : Data} {bits nw Bw : List Bool}
    (h : MainAdapter.CoreInput a bits nw Bw) :
    SubexpEmptyClauseProgram.Ready
      (projectState LeafProgram.Dispatch.registers LeafProgram.Dispatch.stackMap a) := by
  constructor
  · intro i hi
    fin_cases i
    all_goals try norm_num at hi
    all_goals change a.stacks _=[]
    all_goals rw [h]; rfl
  · change a.stacks 796=[]
    simp only [h 796]; rfl

/-- All setup traces and their costs are supplied by concrete programs.  Only
`NativeSupply`, the mass/count service contract, remains to be instantiated. -/
theorem eventually_command_eval :
    ∃ C d p : ℕ, ∀ q : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ (F : ExecCNF.Formula (SAT.Literal (Fin n))) B (nw Bw : List Bool)
        (mass acceptedCount : Cmd 40 896) (a : Data) tailLimit,
      MainAdapter.CoreInput a (Encoding.encodeList id (formulaRecords F)) nw Bw →
      BinaryArithmetic.toNat nw=n → BinaryArithmetic.toNat Bw=B →
      0 < B → F.length ≤ n*B → B ≤ Asymptotic.L n^q →
      NativeSupply F B mass acceptedCount a tailLimit →
      ∃ steps b bit, Eval (command mass acceptedCount) steps a b ∧
      steps ≤ 100*((a.stacks 784).length+1)+7+
        CodeSetupOuterCost.setupMajorant C d q n*
          ((Encoding.encodeList id (formulaRecords F)).length+nw.length+Bw.length+2)^p+tailLimit ∧
      b.stacks 787=[bit] ∧ (bit=true ↔ SAT.Satisfiable (ExecCNF.formulaSet F)) := by
  obtain ⟨C,d,p,hinitial⟩ := initialCode_resource_eval
  refine ⟨C,d,p,?_⟩
  intro q
  filter_upwards [hinitial q] with n hn
  intro F B nw Bw mass acceptedCount a tailLimit hin hnv hBv hB hmn hBn hsupply
  let W := (Encoding.encodeList id (formulaRecords F)).length+nw.length+Bw.length+1
  let initialLimit := CodeSetupOuterCost.setupMajorant C d q n*(W+1)^p
  have hformula : a.stacks 784=Encoding.encodeList id (formulaRecords F) := by
    simp only [hin 784]; rfl
  have hans : a.stacks 787=[] := by simp only [hin 787]; rfl
  have hw : WordBound W a := coreInput_wordBound hin
  obtain ⟨steps,b,bit,he,hsteps,hbit,hsat⟩ := command_of_nontrivial F mass acceptedCount a
    (initialLimit+tailLimit) hformula (coreInput_classifier hin) hans (by
      intro hnonempty hempty
      have hrecords : formulaRecords F≠[] := by
        intro he
        have hh:=congrArg List.length he
        rw [formulaRecords_length,List.length_nil] at hh
        exact hnonempty (List.length_eq_zero_iff.mp hh)
      have hcf : (classified a (formulaRecords F)).stacks=a.stacks := classified_stacks _ _
      have hi := hn (classified a (formulaRecords F)) W (formulaRecords F) B
        (by intro i; rw [hcf]; exact hw i)
        (by intro i hi; rw [hcf]; exact coreInput_empty hin i hi)
        (by rw [hcf]; exact hformula) hrecords hB
        (by rw [hcf,hin 786]; simpa using hBv)
        (by rw [hcf,hin 785]; simpa using hnv)
        (by simpa only [formulaRecords_length] using hmn) hBn
      let P (m : ℕ) : Prop := ∃ ni z, ∃ (s : SparseCode.SuppliedShifts m B)
        (Q : SparseCode.SuppliedLocal m B),
        Eval initialCode ni (classified a (formulaRecords F)) z ∧
        ni ≤ initialLimit ∧ StartReady z n m B ∧
        z.stacks 777=HashSelectProgram.candidateEncoding
          (LeafScopeResourceBounds.initialPayloads (z.stacks 768).length
            (CodeRowsProgram.serializedRows m s Q)) ∧
        WalshExistence.Good (SparseCode.gapDenom m B) s ∧
        SparseCode.HasDistance Q (SparseCode.degree m B/(100*B*SparseCode.logSize m)+1) ∧
        (∀ i : Fin 896, 784 ≤ i.val → i.val < 800 →
          z.stacks i=(classified a (formulaRecords F)).stacks i)
      have hi0 : P (formulaRecords F).length := hi
      have hi1 : P F.length := (formulaRecords_length F) ▸ hi0
      obtain ⟨ni,z,s,Q,hei,hni,hready,hrows,hs,hQ,hframe⟩ := hi1
      have hf : ∀ i : Fin 896, 784 ≤ i.val → i.val < 800 → z.stacks i=a.stacks i := by
        intro i hi hj
        exact (hframe i hi hj).trans (congrFun hcf i)
      obtain ⟨svc,hsvc⟩ := hsupply ni z s Q hei hready hs hQ hrows hf
      obtain ⟨total,out,answer,htotal,hcost,hanswer,hmodels⟩ :=
        nontrivial_from_services (formulaClauses F) (List.length_pos_iff.mpr hnonempty)
          hB mass acceptedCount hei hready s Q hs hQ hrows svc
      exact ⟨total,out,answer,htotal,by dsimp [initialLimit]; omega,hanswer,
        hmodels.trans (formulaClauses_satisfiable F)⟩)
  refine ⟨steps,b,bit,he,?_,hbit,hsat⟩
  simpa only [initialLimit,W,Nat.add_assoc] using hsteps

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
