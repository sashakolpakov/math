import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorBudget
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorBoundsPolynomial

namespace OAI.Algorithms

/-! The exact complete branch budgets admit a common polynomial bound.
Large sparse and incidence buffers are represented by explicit capacity and
live-word caps; none is silently bounded by the original formula bit length. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorBounds
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing SubexpSetupStorage
open HashCircuitProgram HashCircuitProgram.Native MomentsProgram
open IdempotentApplyProgram.Steps NativeSemantics
open PerturbationAssembly
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram

structure NativeCaps {p t n d : ℕ} [Fact p.Prime] (ctx : Context p t n d) (Z : ℕ) : Prop where
  positive : 1 ≤ Z
  dimensionPositive : 0 < d
  width : baseWidth p t ≤ Z
  dimension : d ≤ Z
  ambient : n ≤ Z
  u : ctx.u ≤ Z
  J : ctx.J ≤ Z
  capacity : IdempotentApplyProgram.Bounds.capacity (Finset.univ : Finset (Fin n)) ctx.u ctx.J ≤ Z
  fullWidth : d*baseWidth p t ≤ Z

theorem encodeList_count_le (xs : List (List Bool)) :
    xs.length ≤ (Encoding.encodeList id xs).length := by
  induction xs with
  | nil => simp [Encoding.encodeList]
  | cons x xs ih =>
      simp only [Encoding.encodeList,id_eq,List.length_cons,List.length_append]
      omega

theorem weightedRow_width {n : ℕ} (t d : ℕ)
    (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (HashInputProgram.Expansion.encodedClauses source).length × ZMod 3))
    (K : ℕ) (hs : ∀ ls ∈ source, ls.length ≤ K) :
    ∀ w ∈ HashInputProgram.Expansion.weightedRow t d source terms, w.literals.length ≤ K := by
  intro w hw
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
  exact hs _ (List.getElem_mem _)

theorem total_entries_eq {n B d : ℕ} (payload : ℕ → List Bool)
    (incidence : Fin n → List (Product.Entry n B d))
    (h : ∀ v : Fin n, payload v.val=Product.bytes (incidence v)) :
    incidenceEntries (fun (_ : Unit) (v : Fin n) => payload v.val) ()=Cost.entries incidence := by
  unfold Cost.entries incidenceEntries
  apply List.map_congr_left
  intro v hv
  simp only [h v]

/-- The source component is the checked, explicit native source polynomial.
The remaining branch cost is a fixed ninth-degree polynomial in actual sizes. -/
noncomputable def branchBound {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (n J S A B Z : ℕ) : ℕ :=
  incidencePolynomial p n J S A B+15000000*Z^9

theorem hashBranchBudget_le {r Q n d : ℕ} (p : SourceBank.Parameters r Q d)
    (ctx : Context 3 p.t n d) (f S A B Z : ℕ)
    (minus : RingProgram.Code (Word (baseWidth 3 p.t)) d)
    (one seed : Raw (p:=3) (t:=p.t) (n:=n) (d:=d))
    (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (HashInputProgram.Expansion.encodedClauses source).length × ZMod 3))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode 3 p.t)))
    (b : ℕ) (a : Factor.Data) (payload : ℕ → List Bool)
    (incidence : Fin n → Raw (p:=3) (t:=p.t) (n:=n) (d:=d))
    (hc : NativeCaps ctx Z) (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (hone : Good Finset.univ ctx.u ctx.J one) (hseed : Good Finset.univ ctx.u ctx.J seed)
    (hi : ∀ v, Good Finset.univ ctx.u ctx.J (incidence v))
    (hbytes : ∀ v : Fin n, payload v.val=Product.bytes (incidence v))
    (hf : f ≤ Z) (hb : b ≤ Z) (hraw : (a.stacks 154).length ≤ Z)
    (hmod : (a.stacks 707).length ≤ Z)
    (hsource : (Encoding.encodeList id (HashInputProgram.Expansion.encodedClauses source)).length ≤ Z)
    (hterms : terms.length ≤ Z) (hdigits : digits.length ≤ Z)
    (hwidth : ∀ ls ∈ source, ls.length ≤ Z)
    (ha : WordBound A (projectState Incidence.callerRegisters id (FactorID.output a f)))
    (hstaged : WordBound B (Incidence.staged
      (projectState Incidence.callerRegisters id (FactorID.output a f)))) :
    Factor.hashBranchBudget p ctx f S B minus one seed source terms digits b a payload incidence ≤
      branchBound p n ctx.J S A B Z := by
  let ws := HashInputProgram.Expansion.weightedRow p.t d source terms
  have hws : ws.length ≤ Z := by simpa only [ws,HashInputProgram.Expansion.weightedRow,List.length_map] using hterms
  have hs := hashService_le ctx hu hJ minus one seed incidence hone hseed hi ws digits Z
    (weightedRow_width p.t d source terms Z hwidth)
  have hsp := hashServiceBound_le (baseWidth 3 p.t) d n ctx.u ctx.J
    (IdempotentApplyProgram.Bounds.capacity (Finset.univ : Finset (Fin n)) ctx.u ctx.J)
    Z ws.length digits.length Z hc.positive hc.width hc.dimension hc.ambient hc.u hc.J
    hc.capacity (le_refl _) hws hdigits
  have hservice := hs.trans hsp
  have hexp := expansionBound_le b (a.stacks 707).length
    (HashInputProgram.Expansion.encodedClauses source).length
    (Encoding.encodeList id (HashInputProgram.Expansion.encodedClauses source)).length
    ((d-1+1)*baseWidth 3 p.t) terms.length Z hc.positive hb hmod
    ((encodeList_count_le _).trans hsource) hsource
    (by simpa only [Nat.sub_add_cancel hc.dimensionPositive] using hc.fullWidth) hterms
  change HashInputProgram.Loop.uniformBudget p.t (d-1) b (a.stacks 707)
    (HashInputProgram.Expansion.encodedClauses source) terms.length ≤ _ at hexp
  have hinc := incidence_work_polynomial p
    (projectState Incidence.callerRegisters id (FactorID.output a f)) n ctx.J S A B ha hstaged
  have h0 : 1 ≤ Z^9 := Nat.one_le_pow _ _ hc.positive
  have h1 : Z ≤ Z^9 := by simpa using Nat.pow_le_pow_right hc.positive (show 1 ≤ 9 by decide)
  have h3 : Z^3 ≤ Z^9 := Nat.pow_le_pow_right hc.positive (by decide)
  unfold Factor.hashBranchBudget branchBound
  dsimp only
  rw [total_entries_eq payload incidence hbytes]
  dsimp only [ws] at hservice
  omega

theorem markedBranchBudget_le {r Q n d : ℕ} (p : SourceBank.Parameters r Q d)
    (ctx : Context 3 p.t n d) (f S A B Z : ℕ)
    (minus : RingProgram.Code (Word (baseWidth 3 p.t)) d)
    (one seed : Raw (p:=3) (t:=p.t) (n:=n) (d:=d))
    (ls : List (SAT.Literal (Fin n))) (a : Factor.Data) (payload : ℕ → List Bool)
    (incidence : Fin n → Raw (p:=3) (t:=p.t) (n:=n) (d:=d))
    (hc : NativeCaps ctx Z)
    (hone : Good Finset.univ ctx.u ctx.J one) (hseed : Good Finset.univ ctx.u ctx.J seed)
    (hi : ∀ v, Good Finset.univ ctx.u ctx.J (incidence v))
    (hbytes : ∀ v : Fin n, payload v.val=Product.bytes (incidence v))
    (hf : f ≤ Z) (hraw : (a.stacks 154).length ≤ Z) (hls : ls.length ≤ Z)
    (ha : WordBound A (projectState Incidence.callerRegisters id (FactorID.output a f)))
    (hstaged : WordBound B (Incidence.staged
      (projectState Incidence.callerRegisters id (FactorID.output a f)))) :
    Factor.markedBranchBudget p ctx f S B minus one seed ls a payload incidence ≤
      branchBound p n ctx.J S A B Z := by
  have hs := markedService_le ctx minus one seed incidence hone hseed hi ls
  have hsp := markedServiceBound_le (baseWidth 3 p.t) d n ctx.u ctx.J
    (IdempotentApplyProgram.Bounds.capacity (Finset.univ : Finset (Fin n)) ctx.u ctx.J)
    ls.length Z hc.positive hc.width hc.dimension hc.ambient hc.u hc.J hc.capacity hls
  have hservice := hs.trans hsp
  have hinc := incidence_work_polynomial p
    (projectState Incidence.callerRegisters id (FactorID.output a f)) n ctx.J S A B ha hstaged
  have h0 : 1 ≤ Z^9 := Nat.one_le_pow _ _ hc.positive
  have h1 : Z ≤ Z^9 := by simpa using Nat.pow_le_pow_right hc.positive (show 1 ≤ 9 by decide)
  have h8 : Z^8 ≤ Z^9 := Nat.pow_le_pow_right hc.positive (by decide)
  unfold Factor.markedBranchBudget branchBound
  dsimp only
  rw [total_entries_eq payload incidence hbytes]
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.FactorBounds

end OAI.Algorithms
