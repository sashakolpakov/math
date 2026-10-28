import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorBudgets

/-! The same compact endpoint cap supports the actual tuple controller and
its visitor. Transient scanner/reload work is bounded separately; none of it
is fed back into the retained frame cap between pairs. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial
open SignatureTupleSource SignatureTupleComplete SignatureTupleLoader

private theorem square_le_compact (T : ℕ) : T^2 ≤ HeadSumBudgets.compactCap T := by
  have hp : T*T ≤ FactorTableBudgets.payloadEnvelope T := by
    unfold FactorTableBudgets.payloadEnvelope
    calc
      T*T = T*T*1 := (Nat.mul_one _).symm
      _ ≤ T*T*(2*(T+T+T)+2*T*(2*T)+2) := Nat.mul_le_mul_left _ (by omega)
  unfold HeadSumBudgets.compactCap
  rw [pow_two]
  omega

/-- The fixed degree36 scanner and both persistent frame banks fit the
already chosen compact head cap, including at ambient size zero. -/
theorem retained_le_compact (B A : ℕ) (hB : B ≤ A) :
    retainedEnvelope B 0 ≤ QueryHeadBudgets.compact A := by
  have hsource : 100*(A+2)^2 ≤ QueryHeadBudgets.sourceSize A+1 := by
    have h := Nat.mul_le_mul_right (100*(A+2)^2+2) (show 1 ≤ A+1 by omega)
    unfold QueryHeadBudgets.sourceSize
    omega
  have hpower : (A+2)^36 ≤ (A+2)^40 := Nat.pow_le_pow_right (by omega) (by decide)
  have hscalar : (QueryHeadBudgets.sourceSize A+1)^20 ≤ (QueryHeadBudgets.scalarCap A)^2 := by
    unfold QueryHeadBudgets.scalarCap
    rw [mul_pow,←pow_mul]
    norm_num
  calc
    retainedEnvelope B 0 ≤ (100000*20000^6+10050)*(B+2)^36 := by
      simpa only [Nat.zero_add] using retainedEnvelope_polynomial B 0
    _ ≤ (100000*20000^6+10050)*(A+2)^36 := by gcongr
    _ ≤ 100^20*(A+2)^40 := Nat.mul_le_mul (by norm_num) hpower
    _ = (100*(A+2)^2)^20 := by rw [mul_pow,←pow_mul]
    _ ≤ (QueryHeadBudgets.sourceSize A+1)^20 := Nat.pow_le_pow_left hsource 20
    _ ≤ (QueryHeadBudgets.scalarCap A)^2 := hscalar
    _ ≤ QueryHeadBudgets.compact A := square_le_compact _

/-- Native ready words already supply the numeric source dimensions; no
additional layout, scanner or successful-run premise is required. -/
theorem retainedCap (s : ProducedSource) (A : ℕ) (hs : s.bound ≤ A) :
    RetainedCap s (QueryHeadBudgets.compact A) := by
  have h := retainedEnvelope_cap s 0
  have hle := retained_le_compact s.bound A hs
  exact ⟨h.positive.trans hle,h.cursor.trans hle,h.frames.trans hle,
    h.output.trans hle,h.scanner.trans hle⟩

/-- Source event overhead and all-prefix space, separately from the number
of candidates, attained tuples and callback visits. -/
def eventEnvelope (A : ℕ) : ℕ :=
  scannerEnvelope A+SignatureTupleLoader.runEnvelope A (QueryHeadBudgets.compact A)+
    4000*(QueryHeadBudgets.compact A+1)+200*QueryHeadBudgets.compact A+200

theorem event_bounds (s : ProducedSource) (A : ℕ) (hs : s.bound ≤ A) :
    eventPolynomial s (QueryHeadBudgets.compact A) ≤ eventEnvelope A ∧
    prefixEnvelope s (QueryHeadBudgets.compact A) ≤ eventEnvelope A ∧
    QueryHeadBudgets.compact A ≤ eventEnvelope A := by
  have hscan : scannerEnvelope s.bound ≤ scannerEnvelope A := by
    unfold scannerEnvelope
    gcongr
  have hrun : SignatureTupleLoader.runEnvelope s.bound (QueryHeadBudgets.compact A) ≤
      SignatureTupleLoader.runEnvelope A (QueryHeadBudgets.compact A) := by
    unfold SignatureTupleLoader.runEnvelope
    gcongr
  unfold eventPolynomial prefixEnvelope eventEnvelope
  exact ⟨by omega,by omega,by omega⟩

private theorem compact_ordinary : Ordinary QueryHeadBudgets.compact := by
  obtain ⟨C,e,h⟩ := QueryHeadBudgets.caps_polynomial
  exact ⟨C,e,fun A => (h A).1⟩

private theorem scanner_ordinary : Ordinary scannerEnvelope := by
  unfold scannerEnvelope
  exact ordinary_mul (ordinary_const 100000) (ordinary_pow
    (ordinary_mul (ordinary_const 20000)
      (ordinary_pow (ordinary_add ordinary_id (ordinary_const 2)) 6)) 6)

private theorem run_ordinary : Ordinary (fun A =>
    SignatureTupleLoader.runEnvelope A (QueryHeadBudgets.compact A)) := by
  unfold SignatureTupleLoader.runEnvelope
  exact ordinary_mul (ordinary_const
    (1000*(10000000000000000*HeadLoaderBudgets.sizeCoefficient^8+3)))
    (ordinary_pow (ordinary_add (ordinary_add compact_ordinary ordinary_id) (ordinary_const 2)) 64)

theorem event_polynomial : ∃ C e : ℕ, ∀ A, eventEnvelope A ≤ C*(A+1)^e := by
  change Ordinary eventEnvelope
  unfold eventEnvelope
  exact ordinary_add (ordinary_add (ordinary_add (ordinary_add scanner_ordinary run_ordinary)
    (ordinary_mul (ordinary_const 4000) (ordinary_add compact_ordinary (ordinary_const 1))))
    (ordinary_mul (ordinary_const 200) compact_ordinary)) (ordinary_const 200)

/-- A single fixed coefficient covers local controller events, callback
coefficients and prefix space. The balanced-head exponential stays external. -/
def envelope (A : ℕ) : ℕ := eventEnvelope A+QueryVisitorBudgets.envelope A

theorem envelope_polynomial : ∃ C e : ℕ, ∀ A, envelope A ≤ C*(A+1)^e := by
  change Ordinary envelope
  unfold envelope
  exact ordinary_add event_polynomial QueryVisitorBudgets.envelope_polynomial

/-- Includes the empty-head unit-addition path and the two final setup/guard
steps; it is independent of the number of attained tuples. -/
def runCoefficient (A : ℕ) : ℕ :=
  5*envelope A+2496*QueryHeadBudgets.compact A+QueryVisitorBudgets.tailEnvelope A+1602

private theorem time_bound (P C r K H V : ℕ) (hP : P ≤ C) (hK : 1 ≤ K)
    (hV : V ≤ C*(r+1)*2^H) :
    P+(2*P)*r*K*4^H+K*(V+P)+2 ≤ (5*C+2)*(r+1)*K*4^H := by
  have h4 : 1 ≤ 4^H := one_le_pow₀ (by decide)
  have hpower : 2^H ≤ 4^H := Nat.pow_le_pow_left (by decide) H
  have hR : 1 ≤ (r+1)*K*4^H := by
    simpa only [one_mul] using Nat.mul_le_mul
      (Nat.mul_le_mul (show 1 ≤ r+1 by omega) hK) h4
  have hfirst : P ≤ C*(r+1)*K*4^H := by
    calc
      P ≤ C := hP
      _ = C*1 := (Nat.mul_one _).symm
      _ ≤ C*((r+1)*K*4^H) := Nat.mul_le_mul_left C hR
      _ = _ := by ring
  have hscan : (2*P)*r*K*4^H ≤ (2*C)*(r+1)*K*4^H := by gcongr; omega
  have hvisit : K*V ≤ C*(r+1)*K*4^H := by
    calc
      K*V ≤ K*(C*(r+1)*2^H) := Nat.mul_le_mul_left K hV
      _ ≤ K*(C*(r+1)*4^H) := by gcongr
      _ = _ := by ring
  have hreturn : K*P ≤ C*(r+1)*K*4^H := by
    calc
      K*P ≤ K*C := Nat.mul_le_mul_left K hP
      _ = C*1*K*1 := by ring
      _ ≤ C*(r+1)*K*4^H := by gcongr; omega
  have hfinal : 2 ≤ 2*(r+1)*K*4^H := by
    simpa only [Nat.mul_one,Nat.mul_assoc] using Nat.mul_le_mul_left 2 hR
  calc
    P+(2*P)*r*K*4^H+K*(V+P)+2 ≤
        C*(r+1)*K*4^H+(2*C)*(r+1)*K*4^H+
        (C*(r+1)*K*4^H+C*(r+1)*K*4^H)+2*(r+1)*K*4^H := by
      rw [Nat.mul_add]
      omega
    _ = _ := by ring

/-- Both bounds name the measured quantities of the actual unified native
run, with the unique empty tuple and all losing scans included. -/
theorem run_bounds (s : ProducedSource) {d : ℕ}
    (q : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (A : ℕ)
    (hs : s.bound ≤ A) (hd : d ≤ A) (ht : q.p.t ≤ A) (hu : q.u ≤ A) (hJ : q.J ≤ A)
    (hR : q.p.R = s.input.R) (hw : q.p.width = s.input.width)
    (hp : q.p.power = s.input.power) :
    SignatureTupleRun.completeSpace s q (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.transient A) ≤ runCoefficient A ∧
    ∀ height, SignatureTupleRun.runTime s q (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
      (QueryHeadBudgets.transient A) height ≤
      runCoefficient A*(s.input.r+1)*SignatureTupleRun.tupleCount s.key s.input.r*4^height := by
  have hevent := event_bounds s A hs
  obtain ⟨hvisitor,hspace⟩ := QueryVisitorBudgets.actual_bounds s q A hs hd ht hu hJ hR hw hp
  have hi := OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeTime.inputBounds s.input s.source s.ready s.bound s.bounded
  have htail := QueryVisitorBudgets.tail_le q A (hi.n.trans hs) hd ht hJ
  have hP : eventPolynomial s (QueryHeadBudgets.compact A) ≤ envelope A := by
    unfold envelope
    omega
  constructor
  · unfold SignatureTupleRun.completeSpace SignatureTupleRun.runSpace runCoefficient envelope
    apply max_le
    · exact max_le (by omega) (by omega)
    · omega
  · intro height
    have hV := QueryVisitorSemantics.visitorCost_le s q (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
      (QueryHeadBudgets.transient A) height
    have hv : QueryVisitorSemantics.visitorCost s q (QueryHeadBudgets.compact A)
        (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
        (QueryHeadBudgets.transient A) height ≤ envelope A*(s.input.r+1)*2^height := by
      apply hV.trans
      gcongr
      unfold envelope
      omega
    have hk : 1 ≤ SignatureTupleRun.tupleCount s.key s.input.r := by
      exact prefix_count_positive s.headSize s.key s.input.r
    apply (time_bound _ _ _ _ _ _ hP hk hv).trans
    have hcoeff : 5*envelope A+2 ≤ runCoefficient A := by
      unfold runCoefficient
      omega
    exact Nat.mul_le_mul_right (4^height) (Nat.mul_le_mul_right
      (SignatureTupleRun.tupleCount s.key s.input.r) (Nat.mul_le_mul_right (s.input.r+1) hcoeff))

theorem runCoefficient_polynomial : ∃ C e : ℕ, ∀ A, runCoefficient A ≤ C*(A+1)^e := by
  change Ordinary runCoefficient
  unfold runCoefficient
  have ht : Ordinary QueryVisitorBudgets.tailEnvelope := by
    obtain ⟨C,e,h⟩ := QueryVisitorBudgets.envelope_polynomial
    refine ⟨C,e,fun A => le_trans ?_ (h A)⟩
    unfold QueryVisitorBudgets.envelope
    omega
  exact ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 5) envelope_polynomial)
    (ordinary_mul (ordinary_const 2496) compact_ordinary)) ht) (ordinary_const 1602)

/-- Fixed constants are chosen before every source/input. The rank-controlled
attained tuple count and balanced maximum head exponent remain explicit. -/
theorem complete_polynomial : ∃ C e : ℕ, ∀ (s : ProducedSource) {d : ℕ}
    (q : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (A : ℕ),
    s.bound ≤ A → d ≤ A → q.p.t ≤ A → q.u ≤ A → q.J ≤ A →
    q.p.R = s.input.R → q.p.width = s.input.width → q.p.power = s.input.power →
    RetainedCap s (QueryHeadBudgets.compact A) ∧
    SignatureTupleRun.completeSpace s q (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.transient A) ≤ C*(A+1)^e ∧
    ∀ height, SignatureTupleRun.runTime s q (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
      (QueryHeadBudgets.transient A) height ≤
      C*(A+1)^e*(s.input.r+1)*SignatureTupleRun.tupleCount s.key s.input.r*4^height := by
  obtain ⟨C,e,hpoly⟩ := runCoefficient_polynomial
  refine ⟨C,e,?_⟩
  intro s d q A hs hd ht hu hJ hR hw hp
  obtain ⟨hspace,htime⟩ := run_bounds s q A hs hd ht hu hJ hR hw hp
  refine ⟨retainedCap s A hs,hspace.trans (hpoly A),fun height => ?_⟩
  apply (htime height).trans
  gcongr
  exact hpoly A

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets
