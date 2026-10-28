import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsOutput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsBuckets

namespace OAI.Algorithms

/-! Bridge from explicit head-assignment/support lists to finite-sum semantics.
The only enumeration requirements are no duplicates and exact membership.
The lists may be supplied by the primitive mask and bucket enumerators. -/

namespace SubexponentialSAT.SqrtLog.Moments

open scoped BigOperators
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

variable {V G R : Type*} [DecidableEq V] [CommSemiring R]
  [Fintype G] [DecidableEq G] {X : G → Type*}
  [∀ g, Fintype (X g)] [∀ g, DecidableEq (X g)]
  {vars : Finset V} {t J : ℕ}

def finiteRecords (gs : List G) (xs : ∀ g, List (X g))
    (D : ∀ g, X g → Stored (R := R) vars t J)
    (w : Finset V → ∀ g, X g → R) (s : Finset V) :
    List (List (R × Stored (R := R) vars t J)) :=
  gs.map (fun g => (xs g).map (fun x => (w s g x, D g x)))

omit [DecidableEq V] [CommSemiring R] [Fintype G] [DecidableEq G] [(g : G) → Fintype (X g)] [(g : G) → DecidableEq (X g)] in
@[simp] theorem finiteRecords_length (gs : List G) (xs : ∀ g, List (X g))
    (D : ∀ g, X g → Stored (R := R) vars t J)
    (w : Finset V → ∀ g, X g → R) (s : Finset V) :
    (finiteRecords gs xs D w s).length = gs.length := by simp [finiteRecords]

omit [DecidableEq V] [CommSemiring R] [Fintype G] [DecidableEq G] [(g : G) → Fintype (X g)] [(g : G) → DecidableEq (X g)] in
@[simp] theorem finiteRecords_entries (gs : List G) (xs : ∀ g, List (X g))
    (D : ∀ g, X g → Stored (R := R) vars t J)
    (w : Finset V → ∀ g, X g → R) (s : Finset V) :
    MomentsAlgorithm.entries (finiteRecords gs xs D w s) =
      (gs.map fun g => (xs g).length).sum := by
  simp [MomentsAlgorithm.entries, finiteRecords, List.map_map, Function.comp_def]

theorem records_product (gs : List G) (hgs : gs.Nodup) (hgc : gs.toFinset = Finset.univ)
    (xs : ∀ g, List (X g)) (hxs : ∀ g, (xs g).Nodup)
    (hxc : ∀ g, (xs g).toFinset = Finset.univ)
    (D : ∀ g, X g → Stored (R := R) vars t J)
    (w : Finset V → ∀ g, X g → R) (s : Finset V) :
    ((finiteRecords gs xs D w s).map fun l =>
      (l.map fun a => ringScalar a.1 * a.2.denote).sum).prod =
        ∏ g, ∑ x, ringScalar (w s g x) * (D g x).denote := by
  simp only [finiteRecords, List.map_map, Function.comp_def]
  rw [← List.prod_toFinset (fun g => ((xs g).map
    (fun x => ringScalar (V := V) (w s g x) * (D g x).denote)).sum) hgs, hgc]
  apply Finset.prod_congr rfl
  intro g hg
  rw [← List.sum_toFinset (fun x => ringScalar (V := V) (w s g x) * (D g x).denote)
    (hxs g), hxc g]

theorem run_finite_output (gs : List G) (hgs : gs.Nodup) (hgc : gs.toFinset = Finset.univ)
    (xs : ∀ g, List (X g)) (hxs : ∀ g, (xs g).Nodup)
    (hxc : ∀ g, (xs g).toFinset = Finset.univ)
    (D : ∀ g, X g → Stored (R := R) vars t J)
    (w : Finset V → ∀ g, X g → R)
    (supports : List (Finset V)) (hs : supports.Nodup) :
    PolynomialAlgorithm.denote (outputCoefficients t J
      (MomentsAlgorithm.run Stored.ops (finiteRecords gs xs D w) supports).1.data) =
      Truncation.trunc J (sumUCoeff t
        (∑ s ∈ supports.toFinset, jetCoeff ⟨s⟩ (∏ g, ∑ x,
          ringScalar (w s g x) * (D g x).denote))) := by
  rw [run_output_denote]
  simp_rw [records_product gs hgs hgc xs hxs hxc D w]
  rw [← List.sum_toFinset _ hs]

theorem ringScalar_constant (c : R) :
    ringScalar (V := V) c = jetScalar (jetConstant c) := by
  simp [ringScalar, jetScalar, jetConstant]

/-- The executable finite-list run equals the actual Boolean bucket product.
This is the squarefree head-moment computation used at a node. -/
theorem run_finite_bucket (gs : List G) (hgs : gs.Nodup) (hgc : gs.toFinset = Finset.univ)
    (xs : ∀ g, List (X g)) (hxs : ∀ g, (xs g).Nodup)
    (hxc : ∀ g, (xs g).toFinset = Finset.univ)
    (D : ∀ g, X g → Stored (R := R) vars t J)
    (w : Finset V → ∀ g, X g → R)
    (supports : List (Finset V)) (hs : supports.Nodup)
    (hM : ∀ s : Finset V, s.card < J → s ∈ supports)
    (xval : (∀ g, X g) → V → R)
    (hidem : ∀ x v, xval x v * xval x v = xval x v)
    (hweight : ∀ s x, jetConstant (weight (xval x) s) =
      ∏ g, jetConstant (w s g (x g))) :
    PolynomialAlgorithm.denote (outputCoefficients t J
      (MomentsAlgorithm.run Stored.ops (finiteRecords gs xs D w) supports).1.data) =
      ∑ x : ∀ g, X g, Truncation.trunc J (sumUCoeff t
        (jetEval (xval x) (hidem x) (∏ g, (D g (x g)).denote))) := by
  rw [run_finite_output gs hgs hgc xs hxs hxc D w supports hs]
  let M : Finset (Support V) := supports.toFinset.image Support.mk
  have hMk : ∀ s : Support V, s.vars.card < J → s ∈ M := by
    intro s h
    apply Finset.mem_image.mpr
    exact ⟨s.vars, List.mem_toFinset.mpr (hM s.vars h), by cases s; rfl⟩
  have h := squarefree_head_moments_trunc t J M hMk
    (fun g x => (D g x).denote) (fun g x => (D g x).valid.admissible)
    xval hidem (fun s g x => jetConstant (w s.vars g x)) (fun s x => hweight s.vars x)
  have hinj : Function.Injective (Support.mk : Finset V → Support V) := by
    intro a b h
    exact congrArg Support.vars h
  simpa [M, extractMoments, momentProduct, headMoment,
    Finset.sum_image, hinj.eq_iff, ← ringScalar_constant] using h

end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
