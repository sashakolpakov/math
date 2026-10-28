import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbeddingBranch
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsFinite

namespace OAI.Algorithms

/-! Ambient support enumeration may include supports meeting fixed high
coordinates. Their coefficients are zero, so the output equals the residual
moment computation without any additional Boolean assignments. -/
namespace SubexponentialSAT.SqrtLog.ResidualEmbedding

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators
noncomputable section

variable {V W R : Type*} [DecidableEq V] [DecidableEq W] [CommSemiring R]

@[simp] theorem poly_scalar (e : V ↪ W) (c : R) :
    poly e (Squarefree.scalar c) = Squarefree.scalar c := by
  change poly e (monomial ∅ c) = monomial ∅ c
  simp

@[simp] theorem jet_ringScalar (e : V ↪ W) (c : R) :
    jet e (Moments.ringScalar c) = Moments.ringScalar c := by
  simp [jet, Moments.ringScalar]

/-- Only the image supports contribute, even if the residual polynomial being
extracted depends on the requested ambient support through its weights. -/
theorem sum_jetCoeff (e : V ↪ W) (ambient : Finset (Finset W))
    (residual : Finset (Finset V))
    (hmem : ∀ s, s.map e ∈ ambient ↔ s ∈ residual)
    (F : Finset W → Jet V R) :
    (∑ s ∈ ambient, Moments.jetCoeff ⟨s⟩ (jet e (F s))) =
      ∑ s ∈ residual, Moments.jetCoeff ⟨s⟩ (F (s.map e)) := by
  have himage : residual.image (Finset.map e) ⊆ ambient := by
    intro s hs
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
    exact (hmem a).mpr ha
  calc
    _ = ∑ s ∈ residual.image (Finset.map e), Moments.jetCoeff ⟨s⟩ (jet e (F s)) := by
      symm
      apply Finset.sum_subset himage
      intro s hs hn
      apply jetCoeff_jet_zero
      rintro ⟨a, rfl⟩
      exact hn (Finset.mem_image.mpr ⟨a, (hmem a).mp hs, rfl⟩)
    _ = _ := by
      rw [Finset.sum_image]
      · simp
      · intro a ha b hb h
        exact Finset.map_injective e h

omit [DecidableEq V] [DecidableEq W] in
theorem supportUniverse_mem_map [Fintype V] [Fintype W]
    (e : V ↪ W) (J : ℕ) (s : Finset V) :
    s.map e ∈ Sparse.supportUniverse (Finset.univ : Finset W) J ↔
      s ∈ Sparse.supportUniverse (Finset.univ : Finset V) J := by
  simp [Sparse.supportUniverse]

omit [DecidableEq V] [DecidableEq W] in
/-- Actual Boolean head weights agree on the embedded supports. Values of the
ambient head assignment outside the image cannot affect this product. -/
theorem localBoolWeight_map [Fintype V] [Fintype W]
    {G : Type*} [Fintype G] [DecidableEq G]
    (e : V ↪ W) (head : W → G) (s : Finset V) (g : G)
    (a : Moments.Head head g → Bool) :
    Moments.localBoolWeight (R := R) head ⟨s.map e⟩ g a =
      Moments.localBoolWeight (R := R) (fun v => head (e v)) ⟨s⟩ g
        (fun v => a ⟨e v.val, v.property⟩) := by
  unfold Moments.localBoolWeight
  rw [Finset.prod_map]

section FiniteHeads
variable {G : Type*} [Fintype G] [DecidableEq G] {X : G → Type*}
  [∀ g, Fintype (X g)] [∀ g, DecidableEq (X g)]
  {vars : Finset V} {ambientVars : Finset W} {t J : ℕ}

/-- The native ambient run can use any larger support list with exactly the
required image supports. Extra supports have zero extracted coefficient.
Both computations use the identical head-assignment lists. -/
theorem run_finite_output (e : V ↪ W)
    (gs : List G) (hgs : gs.Nodup) (hgc : gs.toFinset = Finset.univ)
    (xs : ∀ g, List (X g)) (hxs : ∀ g, (xs g).Nodup)
    (hxc : ∀ g, (xs g).toFinset = Finset.univ)
    (D : ∀ g, X g → Moments.Stored (R := R) vars t J)
    (A : ∀ g, X g → Moments.Stored (R := R) ambientVars t J)
    (hA : ∀ g x, (A g x).denote = jet e (D g x).denote)
    (w : Finset V → ∀ g, X g → R) (wa : Finset W → ∀ g, X g → R)
    (hw : ∀ s g x, wa (s.map e) g x = w s g x)
    (supports : List (Finset V)) (hs : supports.Nodup)
    (ambientSupports : List (Finset W)) (ha : ambientSupports.Nodup)
    (hmem : ∀ s, s.map e ∈ ambientSupports ↔ s ∈ supports) :
    PolynomialAlgorithm.denote (Moments.outputCoefficients t J
      (MomentsAlgorithm.run Moments.Stored.ops
        (Moments.finiteRecords gs xs A wa) ambientSupports).1.data) =
    PolynomialAlgorithm.denote (Moments.outputCoefficients t J
      (MomentsAlgorithm.run Moments.Stored.ops
        (Moments.finiteRecords gs xs D w) supports).1.data) := by
  rw [Moments.run_finite_output gs hgs hgc xs hxs hxc A wa ambientSupports ha,
    Moments.run_finite_output gs hgs hgc xs hxs hxc D w supports hs]
  apply congrArg (fun f => Truncation.trunc J (Moments.sumUCoeff t f))
  have hprod (s : Finset W) :
      (∏ g, ∑ x, Moments.ringScalar (wa s g x) * (A g x).denote) =
      jet e (∏ g, ∑ x, Moments.ringScalar (wa s g x) * (D g x).denote) := by
    simp only [map_prod, map_sum, map_mul, jet_ringScalar, hA]
  simp_rw [hprod]
  have hh := sum_jetCoeff e ambientSupports.toFinset supports.toFinset
    (by simpa using hmem)
    (fun s => ∏ g, ∑ x, Moments.ringScalar (wa s g x) * (D g x).denote)
  simpa only [hw] using hh

end FiniteHeads
end
end SubexponentialSAT.SqrtLog.ResidualEmbedding

end OAI.Algorithms
