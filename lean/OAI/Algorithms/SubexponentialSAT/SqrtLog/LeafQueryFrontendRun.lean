import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendPost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendHashCount

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod
open LeafParametersProgram

def frontend (k : ℕ) : Code := .seq countHashes (.seq (coreCommand k) postCommand)
def frontendProgram (k : ℕ) := compiled (frontend k) 700 382

def Query.OutputEmpty (_q : Query) (a : Data) : Prop :=
  Exports.OutputEmpty a ∧ a.stacks 704=[] ∧ a.stacks 134=[] ∧ a.stacks 141=[]

noncomputable def frontendBudget (q : Query) (k : ℕ) (counted prepared beforeClean : Data)
    (tau : List Bool) (l : Fin 8 → ℕ) : ℕ :=
  SubexpScopeCountSetup.countBudget (q.rows.map (HashScopeProgram.RawTable.rowBits q.width.length))+
    coreBudget q k counted tau l+
    postBudget (Execute.guardedModel (q.input k) l) prepared beforeClean
      (highMask q.scopeRows (BinaryArithmetic.toNat q.ambient))

theorem bank_projection_eight (a : Data) (w : Bank.Words)
    (hp : projectState r9 bank a=Execute.state (a.regs ∘ r9) w) :
    projectState Exports.bankRegs Exports.bank a=Bank.state (a.regs ∘ Exports.bankRegs) w := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  exact congrArg StructuredProgram.State.stacks hp

/-- A single native frontend from the formula/row masters. All masks, scope
statistics, numerical parameters, and persistent metadata are produced by the
machine, while the guard bit remains available to the controller. -/
theorem frontend_eval (q : Query) (k : ℕ) (a : Data) (hv : q.Valid)
    (ha : q.Ready a) (ho : q.OutputEmpty a) :
    ∃ n b counted prepared beforeClean tau l w,
      Eval (frontend k) n a b ∧
      n ≤ frontendBudget q k counted prepared beforeClean tau l ∧
      BinaryArithmetic.toNat tau=EarlyThreshold.threshold (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 704=List.replicate q.rows.length true ∧
      b.stacks 718=LeafStatisticsProgram.scopeBits q.scopeRows ∧
      b.stacks 338=highMask q.scopeRows (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 719=q.forward ∧ b.stacks 134=q.forward.map Bool.not ∧
      Exported (Execute.guardedModel (q.input k) l) b ∧
      BinaryArithmetic.toNat (b.stacks 141)=
        2*(Execute.guardedModel (q.input k) l).val 3*
        (8*(Execute.guardedModel (q.input k) l).val 21)^
          (2*(Execute.guardedModel (q.input k) l).val 29) ∧
      projectState Exports.bankRegs Exports.bank b=Bank.state (b.regs ∘ Exports.bankRegs) w ∧
      Circuit.Shape (Execute.guardedModel (q.input k) l) w ∧
      (b.regs 8=true ↔ Guard (q.input k)) ∧ emptyRange b 417 680 ∧
      (∀ i : Fin 768, (i.val < 340 ∨ 680 ≤ i.val) →
        i≠134 → i≠141 → i≠338 → i≠704 → i≠718 → i≠719 →
        (∀ j,Exports.destination j≠i) → b.stacks i=a.stacks i) := by
  obtain ⟨c,hec,hc704,cf⟩ := countHashes_eval a
    (q.rows.map (HashScopeProgram.RawTable.rowBits q.width.length)) ha.2.1 ho.2.1
    (ha.2.2.2.2.2.2.2.1 _ (by decide) (by decide))
    (ha.2.2.2.2.2.2.2.1 _ (by decide) (by decide))
  have hc : q.Ready c := by
    rcases ha with ⟨h700,h701,h705,h706,h707,h708,h709,hz,h338,h718,h719⟩
    refine ⟨(cf _ (by decide)).trans h700,(cf _ (by decide)).trans h701,
      (cf _ (by decide)).trans h705,(cf _ (by decide)).trans h706,
      (cf _ (by decide)).trans h707,(cf _ (by decide)).trans h708,
      (cf _ (by decide)).trans h709,?_,(cf _ (by decide)).trans h338,
      (cf _ (by decide)).trans h718,(cf _ (by decide)).trans h719⟩
    intro i hi hj
    exact (cf i (by intro he; subst i; norm_num at hj)).trans (hz i hi hj)
  obtain ⟨nc,u,tau,l,wu,heu,hnu,htau,hu718,hu338,hu719,hup,hus,hug,hue,huz,uf⟩ :=
    coreCommand_eval q k c hv hc
  have uout : Exports.OutputEmpty u := by
    intro j
    have hd := export_destination_not_private j
    exact (uf _ hd (by fin_cases j <;> decide) (by fin_cases j <;> decide)
      (by fin_cases j <;> decide)).trans ((cf _ (by fin_cases j <;> decide)).trans (ho.1 j))
  have u134 : u.stacks 134=[] := (uf _ (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans
    ((cf _ (by decide)).trans ho.2.2.1)
  have u141 : u.stacks 141=[] := (uf _ (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans
    ((cf _ (by decide)).trans ho.2.2.2)
  have hr : 0 < (Execute.guardedModel (q.input k) l).val 18 := by
    rw [Execute.guardedModel_radius]
    have := produce_r_ge_two (q.input k)
    omega
  have hz : ∀ j,46 ≤ j.val → (Execute.guardedModel (q.input k) l).val j=0 := by
    intro j hj
    simp [Execute.guardedModel,show ¬j.val < 44 by omega]
  obtain ⟨np,b,prepared,beforeClean,w,hep,hnp,hex,hval,h134,hp,hs,hgr,hz,fr⟩ :=
    postCommand_eval u (Execute.guardedModel (q.input k) l) wu hus
      (bank_projection_eight u wu hup) hr hz uout huz u134 u141
      (highMask q.scopeRows (BinaryArithmetic.toNat q.ambient)) hu338
  have bf (i : Fin 768) (hi : i.val < 340 ∨ 680 ≤ i.val) (h134 : i≠134) (h141 : i≠141)
      (hd : ∀ j,Exports.destination j≠i) : b.stacks i=u.stacks i := fr i hi h134 h141 hd
  refine ⟨SubexpScopeCountSetup.countBudget (q.rows.map (HashScopeProgram.RawTable.rowBits q.width.length))+(nc+np),
    b,c,prepared,beforeClean,tau,l,w,hec.seq (heu.seq hep),?_,htau,?_,?_,?_,?_,h134,
    hex,hval,hp,hs,?_,hz,?_⟩
  · unfold frontendBudget; omega
  · exact (bf _ (Or.inr (by decide)) (by decide) (by decide) (by intro j; fin_cases j <;> decide)).trans
      ((uf _ (Or.inr (by decide)) (by decide) (by decide) (by decide)).trans (by simpa using hc704))
  · exact (bf _ (Or.inr (by decide)) (by decide) (by decide) (by intro j; fin_cases j <;> decide)).trans hu718
  · exact (bf _ (Or.inl (by decide)) (by decide) (by decide) (by intro j; fin_cases j <;> decide)).trans hu338
  · exact (bf _ (Or.inr (by decide)) (by decide) (by decide) (by intro j; fin_cases j <;> decide)).trans hu719
  · simpa only [hgr] using hug
  · intro i hi h134 h141 h338 h704 h718 h719 hd
    exact (bf i hi h134 h141 hd).trans ((uf i hi h338 h718 h719).trans (cf i h704))

/-- Compile the exact frontend evaluation with the single paid halt step. -/
theorem frontend_runs_of_eval (k : ℕ) (a b : Data) (n : ℕ)
    (he : Eval (frontend k) n a b) :
    RunsIn (frontendProgram k) (n+1)
      (a.withPC (some (frontendProgram k).entry)) (b.withPC none) :=
  ⟨n+1,le_rfl,compiled_halt_trace he 700 382⟩

theorem frontend_primitive_of_eval (k : ℕ) (a b : Data) (n : ℕ)
    (he : Eval (frontend k) n a b) :
    Computation.RunsIn (primitive (frontendProgram k)).step
      (primitiveOverhead (frontendProgram k)*(n+1))
      (primitiveCfg (frontendProgram k) (a.withPC (some (frontendProgram k).entry)))
      (primitiveCfg (frontendProgram k) (b.withPC none)) :=
  primitive_execution (frontendProgram k) (frontend_runs_of_eval k a b n he)

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
