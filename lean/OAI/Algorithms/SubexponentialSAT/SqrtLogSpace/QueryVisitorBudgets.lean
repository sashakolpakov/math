import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics

/-! Polynomial overhead and prefix space for the complete actual tuple
visitor. The number of heads and the proved maximum head-size exponent stay
explicit; the empty-head/empty-tuple term is retained. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorBudgets
open OAI SqrtLog SubexpLiftRing SubexpSetupStorage
open SignatureTupleSource LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial

/-- Actual final readout and tuple-accumulator addition. -/
def tailEnvelope (A : ℕ) : ℕ :=
  75*QueryHeadBudgets.compact A+97+3000000*(6*A+1)^10

def baselineEnvelope (A : ℕ) : ℕ :=
  QueryVisitorLoad.runEnvelope A (QueryHeadBudgets.compact A)+90*QueryHeadBudgets.compact A+89

/-- One uniform local coefficient covers both representative passes and the
final shared-U readout/addition, as well as their complete source prefix bound. -/
def envelope (A : ℕ) : ℕ :=
  tailEnvelope A+2400*(QueryHeadBudgets.compact A+1)+baselineEnvelope A+
    QueryHeadBudgets.visitorEnvelope A+20

theorem tail_le {r Q n d : ℕ} (q : LeafProgram.Factor.Spec r Q n d) (A : ℕ)
    (hn : n ≤ A) (hd : d ≤ A) (ht : q.p.t ≤ A) (hJ : q.J ≤ A) :
    QueryTupleSum.budget n (baseWidth 3 q.p.t) d q.p.t q.J (QueryHeadBudgets.compact A) ≤
      tailEnvelope A := by
  apply (QueryTupleSum.budget_polynomial n (baseWidth 3 q.p.t) d q.p.t q.J
    (QueryHeadBudgets.compact A)).trans
  unfold tailEnvelope
  simp only [RingProgram.ternary_baseWidth]
  gcongr
  omega

private theorem baseline_le (s : ProducedSource) (A : ℕ) (hs : s.bound ≤ A) :
    QueryVisitorSemantics.baselineCost s (QueryHeadBudgets.compact A) ≤ baselineEnvelope A := by
  unfold QueryVisitorSemantics.baselineCost baselineEnvelope QueryVisitorLoad.runEnvelope
  gcongr

/-- The actual source words, rather than their exponential integer values,
supply every remaining local head coefficient parameter. -/
theorem head_coefficient_le (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (A : ℕ)
    (hs : s.bound ≤ A) (hd : d ≤ A) (ht : q.p.t ≤ A) (hu : q.u ≤ A) (hJ : q.J ≤ A)
    (hR : q.p.R = s.input.R) (hw : q.p.width = s.input.width)
    (hp : q.p.power = s.input.power) :
    QueryVisitorHead.timeCoefficient q s.bound (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A) (QueryHeadBudgets.transient A) ≤
        QueryHeadBudgets.visitorEnvelope A := by
  have hi := NodeTime.inputBounds s.input s.source s.ready s.bound s.bounded
  have hpower : RowSelectionProgram.pairLength q.p.power ≤ A+1 := by
    rw [hp]
    simp only [RowSelectionProgram.pairLength,Native.Inputs.power,
      LayoutProgram.IntegerCache.denominatorWord,List.length_append,List.length_replicate,
      List.length_singleton,List.length_nil,Nat.add_zero]
    have := hi.R
    omega
  have hR' : q.p.R ≤ A := hR ▸ hi.R.trans hs
  have hw' : q.p.width.length ≤ A := hw ▸ hi.width.trans hs
  have hhead := QueryHeadBudgets.visitor_time_coefficient_le q A
    (hi.r.trans hs) (hi.Q.trans hs) (hi.n.trans hs) hd ht hR' hu hJ hw' hpower
  apply le_trans (b := QueryVisitorHead.timeCoefficient q A (QueryHeadBudgets.compact A)
    (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A) (QueryHeadBudgets.transient A)) ?_ hhead
  unfold QueryVisitorHead.timeCoefficient QueryVisitorLoad.runEnvelope
  gcongr

/-- Both measured quantities are the ones returned by the actual visitor
run theorem. Neither side grows with the number of emitted tuples. -/
theorem actual_bounds (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (A : ℕ)
    (hs : s.bound ≤ A) (hd : d ≤ A) (ht : q.p.t ≤ A) (hu : q.u ≤ A) (hJ : q.J ≤ A)
    (hR : q.p.R = s.input.R) (hw : q.p.width = s.input.width)
    (hp : q.p.power = s.input.power) :
    QueryVisitorSemantics.visitorCoefficient s q (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A) (QueryHeadBudgets.transient A) ≤
        envelope A ∧
    QueryVisitorSemantics.visitorSpace s q (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.transient A) ≤ envelope A := by
  have hi := NodeTime.inputBounds s.input s.source s.ready s.bound s.bounded
  have hn := hi.n.trans hs
  have htail := tail_le q A hn hd ht hJ
  have hbase := baseline_le s A hs
  have hhead := head_coefficient_le s q A hs hd ht hu hJ hR hw hp
  have hprefix := QueryHeadBudgets.visitor_prefix_le q A hn hd ht hJ
  have heval : QueryVisitorSemantics.evaluationSpace s q (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.transient A) ≤ QueryHeadBudgets.visitorEnvelope A := by
    apply le_trans (b := max (QueryVisitorLoad.runEnvelope A (QueryHeadBudgets.compact A))
      (max (996*QueryHeadBudgets.compact A+200)
        (max (QueryHeadBudgets.transient A)
          (896*QueryHeadBudgets.compact A+QueryVisitorHead.multiplyBudget q (QueryHeadBudgets.compact A))))) ?_ hprefix
    unfold QueryVisitorSemantics.evaluationSpace QueryVisitorLoad.runEnvelope
    gcongr
  constructor
  · unfold QueryVisitorSemantics.visitorCoefficient envelope
    omega
  · unfold QueryVisitorSemantics.visitorSpace envelope
    exact max_le (by omega) (by omega)

private theorem compact_ordinary : Ordinary QueryHeadBudgets.compact := by
  obtain ⟨C,e,h⟩ := QueryHeadBudgets.caps_polynomial
  exact ⟨C,e,fun A => (h A).1⟩

private theorem tail_ordinary : Ordinary tailEnvelope := by
  unfold tailEnvelope
  exact (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 75) compact_ordinary) (ordinary_const 97)) (ordinary_mul (ordinary_const 3000000) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 6) ordinary_id) (ordinary_const 1)) 10)))

private theorem baseline_ordinary : Ordinary baselineEnvelope := by
  unfold baselineEnvelope QueryVisitorLoad.runEnvelope
  exact (ordinary_add (ordinary_add (ordinary_mul (ordinary_const (1000*(10000000000000000*HeadLoaderBudgets.sizeCoefficient^8+3))) (ordinary_pow (ordinary_add (ordinary_add compact_ordinary ordinary_id) (ordinary_const 2)) 64)) (ordinary_mul (ordinary_const 90) compact_ordinary)) (ordinary_const 89))

theorem envelope_polynomial : ∃ C e : ℕ, ∀ A, envelope A ≤ C*(A+1)^e := by
  change Ordinary envelope
  unfold envelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add tail_ordinary (ordinary_mul (ordinary_const 2400) (ordinary_add compact_ordinary (ordinary_const 1)))) baseline_ordinary) QueryHeadBudgets.visitor_polynomial) (ordinary_const 20))

/-- Uniform fixed constants cover complete visitor time and every source
prefix; the balanced-height exponent and r+1 empty term remain explicit. -/
theorem complete_polynomial : ∃ C e : ℕ, ∀ (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (A : ℕ),
    s.bound ≤ A → d ≤ A → q.p.t ≤ A → q.u ≤ A → q.J ≤ A →
    q.p.R = s.input.R → q.p.width = s.input.width → q.p.power = s.input.power →
    QueryVisitorSemantics.visitorSpace s q (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.transient A) ≤ C*(A+1)^e ∧
    ∀ height, QueryVisitorSemantics.visitorCost s q (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
      (QueryHeadBudgets.transient A) height ≤ C*(A+1)^e*(s.input.r+1)*2^height := by
  obtain ⟨C,e,hpoly⟩ := envelope_polynomial
  refine ⟨C,e,?_⟩
  intro s d q A hs hd ht hu hJ hR hw hp
  obtain ⟨htime,hspace⟩ := actual_bounds s q A hs hd ht hu hJ hR hw hp
  refine ⟨hspace.trans (hpoly A),fun height => ?_⟩
  apply (QueryVisitorSemantics.visitorCost_le s q (QueryHeadBudgets.compact A)
    (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
    (QueryHeadBudgets.transient A) height).trans
  gcongr
  exact htime.trans (hpoly A)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorBudgets
