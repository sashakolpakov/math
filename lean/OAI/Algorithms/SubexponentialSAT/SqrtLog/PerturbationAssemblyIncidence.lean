import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblySource
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramIncidenceFrame

namespace OAI.Algorithms

/-! The complete selected-factor service stages actual masters, constructs
the table, exports it to62 and reclaims its worker, including input556. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls DensePolynomialProgram SubexpSetupStorage
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram

def incidenceOutput (s : OuterStore) (bits : List Bool) : OuterStore :=
  Function.update (Function.update s 556 []) 62 bits

theorem incidence_staged_frame (a : OuterData) (i : Fin 768)
    (hi : i∉LeafProgram.Incidence.workerPorts) :
    (LeafProgram.Incidence.staged a).stacks i=a.stacks i := by
  have hn := mt (LeafProgram.Incidence.mem_workerPorts i).mpr hi
  apply LeafProgram.Incidence.staged_frame
  · intro he; subst i; exact hn (by decide)
  · intro p hp he
    have hd : 340 ≤ p.2.val ∧ p.2.val < 680 := by
      simp only [LeafProgram.Incidence.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    exact hn (he.symm ▸ hd)

theorem incidence_export_restores (a : OuterData) (bits : List Bool) (regs : Fin 16 → Bool)
    (hc : ∀ i : Fin 768,340 ≤ i.val → i.val < 680 → i≠556 → a.stacks i=[])
    (h62 : a.stacks 62=[]) :
    (LeafProgram.Incidence.exported
      (⟨regs,Function.update (LeafProgram.Incidence.staged a).stacks 561 bits⟩ : OuterData)).stacks =
      incidenceOutput a.stacks bits := by
  let b : OuterData := ⟨regs,Function.update (LeafProgram.Incidence.staged a).stacks 561 bits⟩
  change (LeafProgram.Incidence.exported b).stacks=incidenceOutput a.stacks bits
  have hb62 : b.stacks 62=[] := by
    change (LeafProgram.Incidence.staged a).stacks 62=[]
    rw [incidence_staged_frame a 62 (by decide),h62]
  funext i
  by_cases h62i : i=62
  · subst i
    rw [LeafProgram.Incidence.exported_output b hb62]
    simp [b,incidenceOutput]
  rw [incidenceOutput,Function.update_of_ne h62i]
  by_cases h556 : i=556
  · subst i
    rw [Function.update_same]
    exact LeafProgram.Incidence.exported_clean b 556 (by decide)
  rw [Function.update_of_ne h556]
  by_cases hw : i∈LeafProgram.Incidence.workerPorts
  · have hi := (LeafProgram.Incidence.mem_workerPorts i).mp hw
    rw [LeafProgram.Incidence.exported_clean b i hi,hc i hi.1 hi.2 h556]
  · rw [LeafProgram.Incidence.exported_frame b i hw h62i]
    have h561 : i≠561 := by intro he; subst i; exact hw (by decide)
    change Function.update (LeafProgram.Incidence.staged a).stacks 561 bits i=a.stacks i
    rw [Function.update_of_ne h561]
    exact incidence_staged_frame a i hw

def incidenceExportBound (B T : ℕ) : ℕ := 7*T+5+340*(4*(B+T)+3)

theorem incidence_export_bound (a : OuterData) (B T : ℕ)
    (hb : WordBound (B+T) a) (ht : (a.stacks 561).length ≤ T) :
    LeafProgram.Incidence.exportCost a ≤ incidenceExportBound B T := by
  have hc : WordBound (2*(B+T)) (copyState 561 62 a) := by
    intro i
    rw [copyState_stack]
    by_cases hi : i=62
    · subst i
      simp only [Function.update_same,List.length_append]
      have h1:=hb 561
      have h2:=hb 62
      omega
    · rw [Function.update_of_ne hi]
      exact (hb i).trans (by omega)
  have he := clearManyCost_le LeafProgram.Incidence.workerPorts (copyState 561 62 a) _ hc
  have hl : LeafProgram.Incidence.workerPorts.length=340 := by
    simp [LeafProgram.Incidence.workerPorts]
  rw [hl] at he
  unfold LeafProgram.Incidence.exportCost incidenceExportBound
  omega

def incidenceWorkBound {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (a : OuterData) (n J S B : ℕ) : ℕ :=
  LeafProgram.Incidence.stageCost a+
    relFactorWorkPolynomial n (p.R+1) J p.t d
      (((LeafProgram.Incidence.staged a).stacks 532).length+
        ((LeafProgram.Incidence.staged a).stacks 533).length+
        ((LeafProgram.Incidence.staged a).stacks 583).length)
      ((LeafProgram.Incidence.staged a).stacks 574).length
      (LeafProgram.Source.nativeSourceWorkPolynomial p S)+
    incidenceExportBound B (n*literalRecordBound n (incidenceBitsBound n J (d*baseWidth 3 p.t)))

private theorem copy_word_bound {S : ℕ} (src dst : Fin S) (a : SubexpSetupStorage.Data S)
    (B : ℕ) (ha : WordBound B a) : WordBound (2*B) (copyState src dst a) := by
  intro i
  rw [copyState_stack]
  by_cases hi : i=dst
  · subst i
    simp only [Function.update_same,List.length_append]
    have hs:=ha src
    have hd:=ha dst
    omega
  · rw [Function.update_of_ne hi]
    exact (ha i).trans (by omega)

private theorem copies_cost_bound {S : ℕ} (ps : List (Fin S × Fin S))
    (a : SubexpSetupStorage.Data S) (B : ℕ) (ha : WordBound B a) :
    copyManyCost ps a ≤ ps.length*(7*(2^ps.length*B)+5) := by
  induction ps generalizing a B with
  | nil => simp [copyManyCost]
  | cons p ps ih =>
    have h := ih (copyState p.1 p.2 a) (2*B) (copy_word_bound _ _ _ _ ha)
    have hp := ha p.1
    have hb : B ≤ 2^(ps.length+1)*B := by
      calc
        B=1*B := by omega
        _ ≤ 2^(ps.length+1)*B := Nat.mul_le_mul_right _ (Nat.one_le_pow _ _ (by decide))
    calc
      copyManyCost (p::ps) a=(7*(a.stacks p.1).length+5)+
          copyManyCost ps (copyState p.1 p.2 a) := rfl
      _ ≤ (7*(2^ps.length*(2*B))+5)+ps.length*(7*(2^ps.length*(2*B))+5) := by
        apply Nat.add_le_add _ h
        simp only [pow_succ,Nat.mul_assoc] at hb
        omega
      _=(p::ps).length*(7*(2^(p::ps).length*B)+5) := by
        simp only [List.length_cons,pow_succ]
        ring

theorem incidence_stage_bound (a : OuterData) (A : ℕ) (ha : WordBound A a) :
    LeafProgram.Incidence.stageCost a ≤ 40000000*(A+1) := by
  have h := copies_cost_bound LeafProgram.Incidence.pairs a A ha
  have hR := ha 138
  norm_num [LeafProgram.Incidence.pairs] at h
  unfold LeafProgram.Incidence.stageCost
  simp only [LeafProgram.Incidence.pairs]
  omega

def incidencePolynomial {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (n J S A B : ℕ) : ℕ :=
  40000000*(A+1)+
    relFactorWorkPolynomial n (p.R+1) J p.t d (3*B) B
      (LeafProgram.Source.nativeSourceWorkPolynomial p S)+
    incidenceExportBound B (n*literalRecordBound n (incidenceBitsBound n J (d*baseWidth 3 p.t)))

private theorem rel_work_mono (n N J t d E E' H H' K : ℕ)
    (he : E ≤ E') (hh : H ≤ H') :
    relFactorWorkPolynomial n N J t d E H K ≤ relFactorWorkPolynomial n N J t d E' H' K := by
  unfold relFactorWorkPolynomial literalWorkPolynomial lowWorkPolynomial
  dsimp only
  gcongr

theorem incidence_work_polynomial {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (a : OuterData) (n J S A B : ℕ) (ha : WordBound A a)
    (hb : WordBound B (LeafProgram.Incidence.staged a)) :
    incidenceWorkBound p a n J S B ≤ incidencePolynomial p n J S A B := by
  have hstage := incidence_stage_bound a A ha
  have hE : ((LeafProgram.Incidence.staged a).stacks 532).length+
      ((LeafProgram.Incidence.staged a).stacks 533).length+
      ((LeafProgram.Incidence.staged a).stacks 583).length ≤ 3*B := by
    have h0:=hb 532
    have h1:=hb 533
    have h2:=hb 583
    omega
  have hH:=hb 574
  have hwork := rel_work_mono n (p.R+1) J p.t d _ (3*B) _ B
    (LeafProgram.Source.nativeSourceWorkPolynomial p S) hE hH
  unfold incidenceWorkBound incidencePolynomial
  omega


theorem incidence_command_from_source {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (J n f S B : ℕ) (theta : Coeff (baseWidth 3 p.t) d)
    (a : OuterData) (width : List Bool) (frame : Fin 6 → List Bool)
    (h : CallerInput p.t p.model p.modulus p.cache J p.R theta a n)
    (h62 : a.stacks 62=[]) (htmp : a.stacks 684=[])
    (hbase : ∀ i,((LeafProgram.Incidence.staged a).stacks i).length ≤ B)
    (hsize : sourceCallWordBound B n (incidenceBitsBound n J (d*baseWidth 3 p.t)) ≤ S)
    (hn : n ≤ S) (hf : f ≤ S) (hplans : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
    (hsource : ∀ j,j < n → ∀ acc,
      acc.length ≤ n*literalRecordBound n (incidenceBitsBound n J (d*baseWidth 3 p.t)) →
      ((LeafProgram.Incidence.staged a).stacks 574).getD j false=false → ∀ regs,
      SourceCallInput p ps P (sourceCallData (LeafProgram.Incidence.staged a).stacks j acc regs)
        j n f S width frame) :
    ∃ (payload : ℕ → List Bool) (k : ℕ) (rf : Fin 16 → Bool),
      (∀ j,j < n → (payload j).length ≤ incidenceBitsBound n J (d*baseWidth 3 p.t) ∧
        payloadRelation p.t p.model p.modulus p.cache J (p.R+1) theta n
          (sourceRowProperty p ps P n f) (LeafProgram.Incidence.staged a).stacks j (payload j)) ∧
      k ≤ incidenceWorkBound p a n J S B ∧
      Eval LeafProgram.Incidence.command k a
        (⟨rf,incidenceOutput a.stacks (Squarefree.Program.lookupRecords
          (HashCircuitProgram.incidenceEntries
            (fun (_ : Unit) (v : Fin n)=>payload v.val) ()))⟩ : OuterData) := by
  obtain ⟨payload,k,rf,hpayload,hk,he⟩ := staged_command_from_source p ps P J n f S B theta
    a width frame h hbase hsize hn hf hplans hsource (LeafProgram.Incidence.staged a).regs
  let bits := Squarefree.Program.lookupRecords (HashCircuitProgram.incidenceEntries
    (fun (_ : Unit) (v : Fin n)=>payload v.val) ())
  let b : OuterData := ⟨rf,Function.update (LeafProgram.Incidence.staged a).stacks 561 bits⟩
  have hbt : b.stacks 684=[] := by
    change (LeafProgram.Incidence.staged a).stacks 684=[]
    rw [incidence_staged_frame a 684 (by decide),htmp]
  have hrun := LeafProgram.Incidence.command_eval a b k htmp hbt he
  have hout := incidence_export_restores a bits rf h.workerEmpty h62
  have hout' : LeafProgram.Incidence.exported b=
      (⟨(LeafProgram.Incidence.exported b).regs,incidenceOutput a.stacks bits⟩ : OuterData) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · exact hout
  rw [hout'] at hrun
  have ht : bits.length ≤ n*literalRecordBound n (incidenceBitsBound n J (d*baseWidth 3 p.t)) := by
    have hh := rel_tableResult_length_le payload n (incidenceBitsBound n J (d*baseWidth 3 p.t))
      n (by omega) (fun j hj=>(hpayload j hj).1) []
    rw [tableResult_incidence] at hh
    simpa only [List.length_nil,zero_add] using hh
  have hb : WordBound (B+n*literalRecordBound n (incidenceBitsBound n J (d*baseWidth 3 p.t))) b := by
    intro i
    by_cases hi : i=561
    · subst i
      change bits.length ≤ _
      omega
    · change (Function.update (LeafProgram.Incidence.staged a).stacks 561 bits i).length ≤ _
      rw [Function.update_of_ne hi]
      exact (hbase i).trans (by omega)
  have hc := incidence_export_bound b B _ hb (show (b.stacks 561).length ≤ _ from ht)
  refine ⟨payload,_,_,hpayload,?_,hrun⟩
  unfold incidenceWorkBound
  omega

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
