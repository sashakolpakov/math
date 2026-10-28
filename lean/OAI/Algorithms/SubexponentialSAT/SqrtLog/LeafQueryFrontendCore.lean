import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendRawRun
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendHighRun
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendMeasure
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendNumericRun

namespace OAI.Algorithms

/-! Joined per-query core. Mathematical values below describe physical input
words and computed outputs; they are not extra machine inputs. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

structure Query where
  clauses : List (List Bool)
  codes : Fin clauses.length → List ℕ
  rows : HashScopeProgram.RawTable.Rows clauses.length
  mark : Option (Fin clauses.length)
  index : List Bool
  width : List Bool
  modulus : List Bool
  ambient : List Bool

def Query.scopeRows (q : Query) := HashScopeProgram.Complete.scopes 1 0 q.codes q.rows q.mark
def Query.forward (q : Query) := (highMask q.scopeRows (BinaryArithmetic.toNat q.ambient)).reverse

def Query.Valid (q : Query) : Prop :=
  0 < q.width.length ∧ 0 < BinaryArithmetic.toNat q.ambient ∧
  (∀ i, q.clauses[i.val]=Encoding.encodeList Encoding.encodeNat (q.codes i)) ∧
  3*q.clauses.length ≤ 2^q.width.length ∧
  (∀ i, q.mark=some i → q.index=Encoding.encodeNat i.val) ∧
  BinaryArithmetic.toNat q.modulus=q.clauses.length ∧
  (∀ row ∈ q.scopeRows, ∀ v ∈ row, v < BinaryArithmetic.toNat q.ambient)

def Query.Ready (q : Query) (a : Data) : Prop :=
  a.stacks 700=Encoding.encodeList id q.clauses ∧
  a.stacks 701=HashScopeProgram.RawTable.inputBits q.width.length q.rows ∧
  a.stacks 705=q.index ∧ a.stacks 706=[q.mark.isSome] ∧
  a.stacks 707=q.modulus ∧ a.stacks 708=q.width ∧ a.stacks 709=q.ambient ∧
  emptyRange a 340 680 ∧ a.stacks 338=[] ∧ a.stacks 718=[] ∧ a.stacks 719=[]

def Query.input (q : Query) (k : ℕ) : LeafParametersProgram.Input :=
  numericInput q.ambient q.modulus k (totals q.scopeRows q.forward).free
    (totals q.scopeRows q.forward).occurrence (completedArity q.scopeRows q.forward)
    (q.scopeRows.length+(totals q.scopeRows q.forward).uncovered)
    (totals q.scopeRows q.forward).incidences

def coreCommand (k : ℕ) : Code := .seq rawCommand (.seq highCommand
  (.seq measureCommand (.seq (numericStage k) parameterCall)))

noncomputable def coreBudget (q : Query) (k : ℕ) (a : Data) (tau : List Bool) (l : Fin 8 → ℕ) : ℕ :=
  let S := (LeafStatisticsProgram.scopeBits q.scopeRows).length
  let F := q.forward.length
  (copiesCost scopeCopies a+21+HashScopeProgram.Complete.cost 1 0 q.width.length q.modulus
      q.clauses q.codes q.rows q.mark q.index+7*S) +
  (7*q.ambient.length+5+EarlyThreshold.runtimeBound q.ambient+
    (7*S+5+7*q.ambient.length+5+7*tau.length+5)+
    HighIncidenceProgram.Prepare.budget q.scopeRows q.ambient tau+1+17*F+14) +
  (7*S+5+7*F+5+LeafStatisticsProgram.bootBudget q.scopeRows q.forward+
    LeafStatisticsProgram.variableBudget q.scopeRows 0 q.forward+2+
    7*F+5+7*S+5+3+4+RecordPrograms.budget (LeafStatisticsProgram.Arity.cost q.forward)
      (q.scopeRows.map (Encoding.encodeList Encoding.encodeNat))+3*(totals q.scopeRows q.forward).uncovered+10) +
  (7*q.ambient.length+5+7*q.modulus.length+5+2*k.bits.length+1+
    conversionCost (totals q.scopeRows q.forward).free+
    conversionCost (totals q.scopeRows q.forward).occurrence+
    conversionCost (completedArity q.scopeRows q.forward)+
    conversionCost (q.scopeRows.length+(totals q.scopeRows q.forward).uncovered)+
    conversionCost (totals q.scopeRows q.forward).incidences) +
  LeafParametersProgram.Execute.runtimeBound (q.input k) l+1

theorem coreCommand_eval (q : Query) (k : ℕ) (a : Data) (hv : q.Valid) (hready : q.Ready a) :
    ∃ n b tau l w, Eval (coreCommand k) n a b ∧
      n ≤ coreBudget q k a tau l ∧
      BinaryArithmetic.toNat tau=EarlyThreshold.threshold (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 718=LeafStatisticsProgram.scopeBits q.scopeRows ∧
      b.stacks 338=highMask q.scopeRows (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 719=q.forward ∧
      projectState r9 bank b=LeafParametersProgram.Execute.state (b.regs ∘ r9) w ∧
      LeafParametersProgram.Circuit.Shape (LeafParametersProgram.Execute.guardedModel (q.input k) l) w ∧
      (b.regs 8=true ↔ LeafParametersProgram.Guard (q.input k)) ∧
      (LeafParametersProgram.Guard (q.input k) → LeafParametersProgram.Layout.EncodesParameters
        (LeafParametersProgram.produce (q.input k)) w) ∧
      emptyRange b 648 680 ∧
      (∀ i : Fin 768, (i.val < 340 ∨ 680 ≤ i.val) → i≠338 → i≠718 → i≠719 → b.stacks i=a.stacks i) := by
  rcases hv with ⟨hb,hn,hc,hbound,hindex,hm,hids⟩
  rcases hready with ⟨h700,h701,h705,h706,h707,h708,h709,hz,h338,h718,h719⟩
  have ht := hz 679 (by decide) (by decide)
  obtain ⟨nr,r,er,hr718,br,fr⟩ := rawCommand_eval a
    (fun i hi hj => hz i (by omega) (by omega)) ht h718 q.width.length hb q.clauses q.codes hc
    q.rows hbound q.mark q.index q.width q.modulus hindex rfl hm h700 h701 h705 h706 h707 h708
  have r709 : r.stacks 709=q.ambient := (fr 709 (Or.inr (by decide)) (by decide)).trans h709
  have r679 : r.stacks 679=[] := (fr 679 (Or.inr (by decide)) (by decide)).trans ht
  obtain ⟨nh,h,tau,eh,htau,hh338,hh719,bh,fh⟩ := highCommand_eval r q.scopeRows q.ambient r709 hn hr718
    (fun i hi hj => (fr i (Or.inl (by omega)) (by intro he; subst i; omega)).trans (hz i (by omega) (by omega)))
    (fun i hi hj => (fr i (Or.inr (by omega)) (by intro he; subst i; omega)).trans (hz i (by omega) (by omega)))
    r679 ((fr 338 (Or.inl (by decide)) (by decide)).trans h338)
    ((fr 719 (Or.inr (by decide)) (by decide)).trans h719)
    ((fr 645 (Or.inr (by decide)) (by decide)).trans (hz 645 (by decide) (by decide)))
    ((fr 646 (Or.inr (by decide)) (by decide)).trans (hz 646 (by decide) (by decide)))
  have h718 : h.stacks 718=LeafStatisticsProgram.scopeBits q.scopeRows :=
    (fh 718 (Or.inr (by decide)) (Or.inr (by decide)) (by decide) (by decide) (by decide) (by decide)).trans hr718
  have h679 : h.stacks 679=[] :=
    (fh 679 (Or.inr (by decide)) (Or.inr (by decide)) (by decide) (by decide) (by decide) (by decide)).trans r679
  have hlen : q.forward.length=BinaryArithmetic.toNat q.ambient := by simp [Query.forward,highMask]
  obtain ⟨nm,m,em,hmv,bm,fm⟩ := measureCommand_eval h q.scopeRows q.forward h718 hh719 h679
    (fun i hi hj => (fh i (Or.inr (by omega)) (Or.inr (by omega))
      (by intro he; subst i; omega) (by intro he; subst i; omega)
      (by intro he; subst i; omega) (by intro he; subst i; omega)).trans
        ((fr i (Or.inr (by omega)) (by intro he; subst i; omega)).trans (hz i (by omega) (by omega))))
    (by simpa only [hlen] using hids)
  have mhframe (i : Fin 768) (hi : i.val < 340 ∨ 680 ≤ i.val) (h338 : i≠338) (h719 : i≠719) : m.stacks i=r.stacks i := by
    exact (fm i (by omega)).trans (fh i (by omega) (by omega) h338 h719
      (by intro he; subst i; omega) (by intro he; subst i; omega))
  have m709 : m.stacks 709=q.ambient := (mhframe 709 (Or.inr (by decide)) (by decide) (by decide)).trans r709
  have m707 : m.stacks 707=q.modulus := (mhframe 707 (Or.inr (by decide)) (by decide) (by decide)).trans
    ((fr 707 (Or.inr (by decide)) (by decide)).trans h707)
  have m679 : m.stacks 679=[] := (fm 679 (Or.inr (by decide))).trans h679
  have m647 : m.stacks 647=[] := (fm 647 (Or.inr (by decide))).trans
    ((fh 647 (Or.inr (by decide)) (Or.inr (by decide)) (by decide) (by decide) (by decide) (by decide)).trans
      ((fr 647 (Or.inr (by decide)) (by decide)).trans (hz 647 (by decide) (by decide))))
  rcases hmv with ⟨mf,mo,mi,mq,ma⟩
  obtain ⟨nn,u,l,w,en,hup,hushape,bn,fn⟩ := numericStage_eval m q.ambient q.modulus k
    (totals q.scopeRows q.forward).free (totals q.scopeRows q.forward).occurrence
    (completedArity q.scopeRows q.forward) (q.scopeRows.length+(totals q.scopeRows q.forward).uncovered)
    (totals q.scopeRows q.forward).incidences m709 m707
    (fun i hi hj => (fm i (Or.inl (by omega))).trans
      ((fh i (Or.inl (by omega)) (Or.inl (by omega)) (by intro he; subst i; omega)
        (by intro he; subst i; omega) (by intro he; subst i; omega) (by intro he; subst i; omega)).trans
        ((fr i (Or.inl (by omega)) (by intro he; subst i; omega)).trans (hz i hi (by omega)))))
    m679 m647 mf mo ma mq mi
  obtain ⟨np,bp,rp,wp,ep,hguard,hshape,hparameters⟩ := parameterCall_eval u (q.input k) l w hushape hup
  let b := embedState r9 bank u (LeafParametersProgram.Execute.state rp wp)
  have fb (i : Fin 768) (hi : i.val < 340 ∨ 417 ≤ i.val) : b.stacks i=u.stacks i :=
    embedded_stack_frame (by decide) (by decide) u _ i hi
  have fnu (i : Fin 768) (hi : i.val < 340 ∨ 680 ≤ i.val) : u.stacks i=m.stacks i :=
    fn i (by omega) (by intro he; subst i; omega) (by intro he; subst i; omega)
      (by intro he; subst i; omega) (by intro he; subst i; omega) (by intro he; subst i; omega)
      (by intro he; subst i; omega)
  have b718 : b.stacks 718=LeafStatisticsProgram.scopeBits q.scopeRows :=
    (fb 718 (Or.inr (by decide))).trans ((fnu 718 (Or.inr (by decide))).trans
      ((fm 718 (Or.inr (by decide))).trans h718))
  have b338 : b.stacks 338=highMask q.scopeRows (BinaryArithmetic.toNat q.ambient) :=
    (fb 338 (Or.inl (by decide))).trans ((fnu 338 (Or.inl (by decide))).trans
      ((fm 338 (Or.inl (by decide))).trans hh338))
  have b719 : b.stacks 719=q.forward := (fb 719 (Or.inr (by decide))).trans
    ((fnu 719 (Or.inr (by decide))).trans ((fm 719 (Or.inr (by decide))).trans hh719))
  have pb : projectState r9 bank b=LeafParametersProgram.Execute.state rp wp :=
    projectState_embed _ _ _ _ (registers_injective ..) (block_injective ..)
  have rb : b.regs ∘ r9=rp := congrArg StructuredProgram.State.regs pb
  refine ⟨nr+(nh+(nm+(nn+np))),b,tau,l,wp,er.seq (eh.seq (em.seq (en.seq ep))),?_,htau,
    b718,b338,b719,?_,hshape,?_,hparameters,?_,?_⟩
  · change h.stacks 719=q.forward at hh719
    have hcopy : copiesCost statsCopies h=7*(LeafStatisticsProgram.scopeBits q.scopeRows).length+5+7*q.forward.length+5 := by
      simp [copiesCost,statsCopies,copied_stack,h718,hh719]
      omega
    rw [measureBudget,hcopy] at bm
    unfold coreBudget
    dsimp only
    dsimp only [Query.scopeRows,Query.forward] at br bh bm bn ⊢
    simp only [List.length_reverse] at br bh bm bn ⊢
    omega
  · rw [rb]; exact pb
  · have hr8 : b.regs 8=rp 8 := congrFun rb 8
    simpa only [hr8] using hguard
  · intro i hi hj
    have hb_u := fb i (Or.inr (by omega))
    have hu_m := fn i (Or.inr (by omega))
      (by intro he; subst i; omega) (by intro he; subst i; omega)
      (by intro he; subst i; omega) (by intro he; subst i; omega)
      (by intro he; subst i; omega) (by intro he; subst i; omega)
    have hm_h := fm i (Or.inr (by omega))
    have hh_r := fh i (Or.inr (by omega)) (Or.inr (by omega))
      (by intro he; subst i; omega) (by intro he; subst i; omega)
      (by intro he; subst i; omega) (by intro he; subst i; omega)
    have hr_a := fr i (Or.inr (by omega)) (by intro he; subst i; omega)
    exact hb_u.trans (hu_m.trans (hm_h.trans (hh_r.trans (hr_a.trans (hz i (by omega) hj)))))
  · intro i hi h338 h718 h719
    exact (fb i (by omega)).trans ((fnu i hi).trans ((mhframe i hi h338 h719).trans
      (fr i (by omega) h718)))

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
