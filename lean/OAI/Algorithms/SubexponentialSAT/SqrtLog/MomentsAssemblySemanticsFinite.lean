import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblySemanticsLoops
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbeddingMoments

namespace OAI.Algorithms

/-! Finite-list adapters for the actual assembly recurrences. Each native head
contains the encoded list of assignments to that head. All bridges below keep
this assignment type explicit, including when jets use ambient variable IDs. -/
namespace SubexponentialSAT.SqrtLog.MomentsAssembly
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators

variable {R : Type*} [CommRing R]
variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
  (cache : RingProgram.ScalarCache p t) {n d : ℕ}
  (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
  (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
  (htable : ∀ i j, basis i * basis j =
    ∑ k, scalar (SubexpQuarticRing.wordValue p t (table i j k)) * basis k)
  (u J : ℕ)
  (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)

variable {G : Type*} {X : G → Type*} {vars : Finset (Fin n)}
  (gs : List G) (xs : ∀ g, List (X g)) (input : G → HeadInput)
  (encode : ∀ g, X g → List Bool)
  (hxs : ∀ g, (input g).assignments = (xs g).map (encode g))
  (D : ∀ g, X g → Moments.Stored (R := R) vars u J)
  (w : Finset (Fin n) → ∀ g, X g → R)
  (high : Fin 768 → List Bool)

include hxs

/- A contract only for individual emitted assignment records suffices to
identify every native head sum with the finite-record list interpreter. -/
theorem heads_eq_finiteRecords (s : Finset (Fin n))
    (hm : ∀ g ∈ gs, ∀ x ∈ xs g,
      contributionDenote p t M cache scalar basis
        (meaning (headContext (Function.update high 168 (encodeMask s)) (input g)) (encode g x)) =
        Moments.ringScalar (w s g x) * (D g x).denote) :
    ((gs.map input).map (headDenote p t M cache scalar basis meaning
      (Function.update high 168 (encodeMask s)))) =
      ((Moments.finiteRecords gs xs D w s).map fun l =>
        (l.map fun a => Moments.ringScalar a.1 * a.2.denote).sum) := by
  simp only [List.map_map, Moments.finiteRecords, Function.comp_def]
  apply List.map_congr_left
  intro g hg
  unfold headDenote
  rw [hxs g, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x hx
  exact hm g hg x hx

include htable in
theorem supportsRun_finite_output_eq
    (one : List (Product.Entry n (baseWidth p t) d)) (ss : List (Finset (Fin n)))
    (ho : denote p t M cache scalar basis one = canonical u J 1)
    (hm : ∀ s ∈ ss, ∀ g ∈ gs, ∀ x ∈ xs g,
      contributionDenote p t M cache scalar basis
        (meaning (headContext (Function.update high 168 (encodeMask s)) (input g)) (encode g x)) =
        Moments.ringScalar (w s g x) * (D g x).denote) :
    PolynomialAlgorithm.denote (Moments.outputCoefficients u J
      (MomentsProgram.Dictionary.denoteTable (coefficient p t M cache scalar basis)
        (supportsRun p t M cache table u J meaning high (gs.map input) one ss []))) =
      PolynomialAlgorithm.denote (Moments.outputCoefficients u J
        (MomentsAlgorithm.run Moments.Stored.ops (Moments.finiteRecords gs xs D w) ss).1.data) := by
  apply supportsRun_output_eq_run p t M cache scalar basis table htable u J meaning
    high (gs.map input) one ss ho
  intro s hs
  exact heads_eq_finiteRecords p t M cache scalar basis u J meaning
    gs xs input encode hxs D w high s (hm s hs)

include htable in
theorem supportsRun_finite_bucket [Fintype G] [DecidableEq G]
    [∀ g, Fintype (X g)] [∀ g, DecidableEq (X g)]
    (hgs : gs.Nodup) (hgc : gs.toFinset = Finset.univ)
    (hxn : ∀ g, (xs g).Nodup) (hxc : ∀ g, (xs g).toFinset = Finset.univ)
    (one : List (Product.Entry n (baseWidth p t) d)) (ss : List (Finset (Fin n)))
    (hs : ss.Nodup) (hM : ∀ s : Finset (Fin n), s.card < J → s ∈ ss)
    (ho : denote p t M cache scalar basis one = canonical u J 1)
    (hm : ∀ s ∈ ss, ∀ g ∈ gs, ∀ x ∈ xs g,
      contributionDenote p t M cache scalar basis
        (meaning (headContext (Function.update high 168 (encodeMask s)) (input g)) (encode g x)) =
        Moments.ringScalar (w s g x) * (D g x).denote)
    (xval : (∀ g, X g) → Fin n → R)
    (hidem : ∀ x v, xval x v * xval x v = xval x v)
    (hweight : ∀ s x, Moments.jetConstant (Squarefree.weight (xval x) s) =
      ∏ g, Moments.jetConstant (w s g (x g))) :
    PolynomialAlgorithm.denote (Moments.outputCoefficients u J
      (MomentsProgram.Dictionary.denoteTable (coefficient p t M cache scalar basis)
        (supportsRun p t M cache table u J meaning high (gs.map input) one ss []))) =
      ∑ x : ∀ g, X g, Truncation.trunc J (Moments.sumUCoeff u
        (Moments.jetEval (xval x) (hidem x) (∏ g, (D g (x g)).denote))) := by
  rw [supportsRun_finite_output_eq p t M cache scalar basis table htable u J meaning
    gs xs input encode hxs D w high one ss ho hm]
  exact Moments.run_finite_bucket gs hgs hgc xs hxn hxc D w ss hs hM xval hidem hweight

/- Ambient IDs are only an encoding of free-variable jets. The finite
assignment type stays unchanged during transport to the free universe. -/
include htable in
theorem supportsRun_embedded_finite_bucket {V : Type*} [DecidableEq V]
    [Fintype G] [DecidableEq G] [∀ g, Fintype (X g)] [∀ g, DecidableEq (X g)]
    (e : V ↪ Fin n) {freeVars : Finset V}
    (F : ∀ g, X g → Moments.Stored (R := R) freeVars u J)
    (wf : Finset V → ∀ g, X g → R)
    (hD : ∀ g x, (D g x).denote = ResidualEmbedding.jet e (F g x).denote)
    (hw : ∀ s g x, w (s.map e) g x = wf s g x)
    (hgs : gs.Nodup) (hgc : gs.toFinset = Finset.univ)
    (hxn : ∀ g, (xs g).Nodup) (hxc : ∀ g, (xs g).toFinset = Finset.univ)
    (one : List (Product.Entry n (baseWidth p t) d)) (ss : List (Finset (Fin n)))
    (freeSupports : List (Finset V)) (hs : ss.Nodup) (hf : freeSupports.Nodup)
    (hmem : ∀ s, s.map e ∈ ss ↔ s ∈ freeSupports)
    (hM : ∀ s : Finset V, s.card < J → s ∈ freeSupports)
    (ho : denote p t M cache scalar basis one = canonical u J 1)
    (hm : ∀ s ∈ ss, ∀ g ∈ gs, ∀ x ∈ xs g,
      contributionDenote p t M cache scalar basis
        (meaning (headContext (Function.update high 168 (encodeMask s)) (input g)) (encode g x)) =
        Moments.ringScalar (w s g x) * (D g x).denote)
    (xval : (∀ g, X g) → V → R)
    (hidem : ∀ x v, xval x v * xval x v = xval x v)
    (hweight : ∀ s x, Moments.jetConstant (Squarefree.weight (xval x) s) =
      ∏ g, Moments.jetConstant (wf s g (x g))) :
    PolynomialAlgorithm.denote (Moments.outputCoefficients u J
      (MomentsProgram.Dictionary.denoteTable (coefficient p t M cache scalar basis)
        (supportsRun p t M cache table u J meaning high (gs.map input) one ss []))) =
      ∑ x : ∀ g, X g, Truncation.trunc J (Moments.sumUCoeff u
        (Moments.jetEval (xval x) (hidem x) (∏ g, (F g (x g)).denote))) := by
  rw [supportsRun_finite_output_eq p t M cache scalar basis table htable u J meaning
    gs xs input encode hxs D w high one ss ho hm]
  rw [ResidualEmbedding.run_finite_output e gs hgs hgc xs hxn hxc F D hD wf w hw
    freeSupports hf ss hs hmem]
  exact Moments.run_finite_bucket gs hgs hgc xs hxn hxc F wf freeSupports hf hM xval hidem hweight

end SubexponentialSAT.SqrtLog.MomentsAssembly

end OAI.Algorithms
