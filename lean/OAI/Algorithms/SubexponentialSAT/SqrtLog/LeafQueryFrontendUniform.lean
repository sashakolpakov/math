import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendRun
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendInputBudget
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendPostBound
import OAI.Algorithms.SubexponentialSAT.SubexpPrimeProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

def Query.hashCountBudget (q : Query) : ℕ :=
  SubexpScopeCountSetup.countBudget (q.rows.map (HashScopeProgram.RawTable.rowBits q.width.length))

noncomputable def Query.inputBudget (q : Query) (k : ℕ) : ℕ :=
  q.hashCountBudget+q.coreInputBudget k+
    postUniformBudget (Execute.guardedModel (q.input k) (q.inputLengths k))
      (BinaryArithmetic.toNat q.ambient) (q.coreInputBudget k)

/-- The actual frontend has a bound depending only on its physical input query
and the fixed formula width. No intermediate state or computed padding witness
occurs in this bound. -/
theorem frontend_eval_input_bound (q : Query) (k : ℕ) (a : Data) (hv : q.Valid)
    (ha : q.Ready a) (ho : q.OutputEmpty a) :
    ∃ n b, Eval (frontend k) n a b ∧ n ≤ q.inputBudget k := by
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
  obtain ⟨nc,u,tau,l,wu,heu,hnu,htau,hu718,hu338,hu719,hup,hus,hug,hue,huz,uf,htlen,hll⟩ :=
    coreCommand_eval_bounded q k c hv hc
  subst l
  have hnc : nc ≤ q.coreInputBudget k := hnu.trans
    (coreBudget_le_input q k c hc hv.2.1 tau htau htlen)
  have uout : Exports.OutputEmpty u := by
    intro j
    have hd := export_destination_not_private j
    exact (uf _ hd (by fin_cases j <;> decide) (by fin_cases j <;> decide)
      (by fin_cases j <;> decide)).trans ((cf _ (by fin_cases j <;> decide)).trans (ho.1 j))
  have u134 : u.stacks 134=[] := (uf _ (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans
    ((cf _ (by decide)).trans ho.2.2.1)
  have u141 : u.stacks 141=[] := (uf _ (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans
    ((cf _ (by decide)).trans ho.2.2.2)
  have hr : 0 < (Execute.guardedModel (q.input k) (q.inputLengths k)).val 18 := by
    rw [Execute.guardedModel_radius]
    have := produce_r_ge_two (q.input k)
    omega
  have hz : ∀ j,46 ≤ j.val → (Execute.guardedModel (q.input k) (q.inputLengths k)).val j=0 := by
    intro j hj
    simp [Execute.guardedModel,show ¬j.val < 44 by omega]
  have hul : ∀ i∈cleanupPorts, (u.stacks i).length ≤ q.coreInputBudget k := by
    intro i hi
    have hib := (cleanup_mem i).mp hi
    have hci : c.stacks i=[] := hc.2.2.2.2.2.2.2.1 i (by omega) (by omega)
    have hg := eval_length_le heu i
    rw [hci,List.length_nil,zero_add] at hg
    exact hg.trans hnc
  obtain ⟨np,b,hep,hnp⟩ := postCommand_eval_uniform u
    (Execute.guardedModel (q.input k) (q.inputLengths k)) wu hus
    (bank_projection_eight u wu hup) hr hz uout huz u134 u141
    (highMask q.scopeRows (BinaryArithmetic.toNat q.ambient)) hu338
    (q.coreInputBudget k) hul
  refine ⟨q.hashCountBudget+(nc+np),b,hec.seq (heu.seq hep),?_⟩
  have hlen : (highMask q.scopeRows (BinaryArithmetic.toNat q.ambient)).length=
      BinaryArithmetic.toNat q.ambient := by simp [highMask]
  rw [hlen] at hnp
  unfold Query.inputBudget
  omega

/-- The input bound applies to every occurrence of the frontend in a larger
execution, by uniqueness of its deterministic instruction count. -/
theorem frontend_time_le (q : Query) (k : ℕ) {a b : Data} {n : ℕ}
    (hv : q.Valid) (ha : q.Ready a) (ho : q.OutputEmpty a)
    (he : Eval (frontend k) n a b) : n ≤ q.inputBudget k := by
  obtain ⟨m,c,hm,hb⟩ := frontend_eval_input_bound q k a hv ha ho
  exact (SubexpPrimeProgram.eval_steps_unique he hm 700 382) ▸ hb

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
