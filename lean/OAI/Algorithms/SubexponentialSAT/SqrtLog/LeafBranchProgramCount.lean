import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgramRun
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramRank

namespace OAI.Algorithms

/-! Disjointness of the high-coordinate partition turns the native rank sum
into a full count over the original assignment space. -/
namespace SubexponentialSAT.SqrtLog.LeafBranchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open scoped BigOperators

 theorem rankSum_eq_sum (value : ℕ → ℕ) (n : ℕ) :
    rankSum value 0 n = ∑ r : Fin n, value r.val := by
  rw [Fin.sum_univ_eq_sum_range, rankSum, ← List.range_eq_range']
  induction n with
  | zero => simp
  | succ n ih => simp [List.sum_range_succ, Finset.sum_range_succ, ih]

theorem rankSum_original {V : Type*} [Fintype V] [DecidableEq V]
    (H : Finset V) (order : Fin H.card ≃ H) (P : (V → Bool) → Prop) [DecidablePred P]
    (value : ℕ → ℕ)
    (hvalue : ∀ r : Fin (2^H.card), value r.val =
      ∑ b : {v : V // v ∉ H} → Bool,
        if P (HighIncidence.glue H (HighIncidenceProgram.Rank.highEquiv order r) b) then 1 else 0) :
    rankSum value 0 (2^H.card) = ∑ x : V → Bool, if P x then 1 else 0 := by
  rw [rankSum_eq_sum, HighIncidenceProgram.Rank.sum_original_by_rank H order]
  apply Finset.sum_congr rfl
  intro r _
  exact hvalue r

/-- This theorem counts every original assignment exactly once. The inputs are
an actual measured residual program and its per-branch correctness proof. -/
theorem enumerate_full_count {R S : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (p : Ports R S) (query : Cmd R S) (H : Finset V) (order : Fin H.card ≃ H)
    (P : (V → Bool) → Prop) [DecidablePred P]
    (I : State R S → Prop) (budget width : ℕ) (value : ℕ → ℕ)
    (cs : CounterForPrograms.FrameStable p.counter (fun _ => I))
    (ms : MassStable p I)
    (spec : ResidualSpec p query (List.replicate H.card 1) I budget width value)
    (hvalue : ∀ r : Fin (2^H.card), value r.val =
      ∑ b : {v : V // v ∉ H} → Bool,
        if P (HighIncidence.glue H (HighIncidenceProgram.Rank.highEquiv order r) b) then 1 else 0)
    (a : State R S) (hi : Ready p I a)
    (hc : a.stacks p.counter.counter = Encoding.encodeList id (List.replicate H.card [false]))
    (hs : a.stacks p.counter.scratch = []) (ha : read p a = []) :
    ∃ n b, Eval (ExecCNFTupleEnumeration.enumerate p.counter (body p query)) (1+n) a b ∧
      Ready p I b ∧ b.stacks p.counter.scratch = [] ∧
      (read p b).length ≤ 2^H.card*(width+1) ∧
      BinaryArithmetic.toNat (read p b) = (∑ x : V → Bool, if P x then 1 else 0) ∧
      1+n ≤ 2^H.card*(budget+16*(2^H.card*(width+1)+1)+28*H.card+15)+2 := by
  obtain ⟨n,b,he,hv,hbi,hbs,hlen,hval,hn⟩ :=
    enumerate_sum p query (List.replicate H.card 1) I budget width value cs ms spec
      (List.replicate H.card [false]) a (by simp) hi hc hs
      (by simp)
  have hflat : (List.replicate H.card [false]).flatten.length = H.card := by simp
  have henc : (Encoding.encodeList id (List.replicate H.card [false])).length = 4*H.card+1 := by
    rw [ExecCNFTupleOdometer.encoded_length,hflat,List.length_replicate]
    omega
  rw [hflat,ha] at hlen hval hn
  rw [henc] at hn
  simp only [List.length_nil,zero_add,BinaryArithmetic.toNat] at hlen hval hn
  refine ⟨n,b,he,hbi,hbs,hlen,?_,?_⟩
  · exact hval.trans (rankSum_original H order P value hvalue)
  · convert hn using 1 ; ring

end SubexponentialSAT.SqrtLog.LeafBranchProgram

end OAI.Algorithms
