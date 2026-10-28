import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Counting
import OAI.Algorithms.SubexponentialSAT.SubexpGlobalPolynomial
import OAI.Algorithms.SubexponentialSAT.SubexpSeparation
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutSpec
import OAI.Algorithms.SubexponentialSAT.SubexpActualRing
import OAI.Algorithms.SubexponentialSAT.SubexpExplicitLift

namespace OAI.Algorithms

/-!
# Exact counting with arbitrarily many symbolic color groups

This module preserves the binary-color proof in `Counting` and gives the
Section 4 computation with an arbitrary finite color type. The number of
colors is not fixed in the statements. All sums, products, truncations, and
coefficient extractions are defined before their correctness is proved.
-/

namespace SubexponentialSAT.SubexpCounting

noncomputable section

open scoped BigOperators

abbrev Poly (ι R : Type*) [CommSemiring R] := Truncation.Poly ι R

section Local

variable {ι Ω O G R : Type*} {X : O → G → Type*}
  [CommSemiring R] [Fintype ι] [Fintype Ω] [Fintype O]
  [Fintype G] [DecidableEq G] [∀ o g, Fintype (X o g)]

/-- The canonical representative of one full symbolic color group. -/
def group (μ D : ℕ) (P : G → Ω → Poly ι R) (g : G) (z : Ω) : Poly ι R :=
  Truncation.canonical μ D (D + μ) (P g z)

/-- Multiply all separately truncated groups and reduce again. -/
def groupProduct (μ D : ℕ) (P : G → Ω → Poly ι R) (z : Ω) : Poly ι R :=
  Truncation.canonical μ D (D + μ) (∏ g, group μ D P g z)

/-- Equation (4.6): one outer scalar times the product of the independent
inner sums, reduced to its canonical representative. -/
def separatedMoment (μ D : ℕ) (e : Ω ≃ Σ o, ∀ g, X o g)
    (reps : ∀ o g, X o g) (P : G → Ω → Poly ι R)
    (c : O → R) (wg : ∀ o g, X o g → R) : Poly ι R :=
  Truncation.canonical μ D (D + μ)
    (∑ o, WeightedSupport.scalarHom (c o) * ∏ g,
      ∑ y : X o g, WeightedSupport.scalarHom (wg o g y) *
        group μ D P g (e.symm ⟨o, Function.update (reps o) g y⟩))

/-- Equation (4.5): extract each matching X monomial and only then set U=1. -/
def separatedJet (μ D : ℕ) (e : Ω ≃ Σ o, ∀ g, X o g)
    (reps : ∀ o g, X o g) (P : G → Ω → Poly ι R)
    (c : (ι →₀ ℕ) → O → R)
    (wg : (ι →₀ ℕ) → ∀ o g, X o g → R) : Polynomial R :=
  ∑ a ∈ Moments.retained (D + μ),
    (Counting.extractX a (separatedMoment μ D e reps P (c a) (wg a))).eval 1

omit [Fintype ι] [Fintype Ω] [DecidableEq G] in
/-- The product in the quotient has the canonical representative of the
full product, regardless of the number of color groups. -/
theorem groupProduct_eq (μ D : ℕ) (P : G → Ω → Poly ι R) (z : Ω) :
    groupProduct μ D P z = Truncation.canonical μ D (D + μ) (∏ g, P g z) :=
  SubexpGlobalPolynomial.canonical_prod μ D (D + μ) Finset.univ (fun g => P g z)

omit [Fintype ι] in
/-- Finite distributivity identifies the actual separated computation with
the full symbolic moment. The hypothesis is only own-coordinate dependence. -/
theorem separatedMoment_eq_sum (μ D : ℕ)
    (e : Ω ≃ Σ o, ∀ g, X o g) (reps : ∀ o g, X o g)
    (P : G → Ω → Poly ι R) (w : Ω → R)
    (c : O → R) (wg : ∀ o g, X o g → R)
    (hP : ∀ o g x y, x g = y g → P g (e.symm ⟨o, x⟩) = P g (e.symm ⟨o, y⟩))
    (hw : ∀ o x, w (e.symm ⟨o, x⟩) = c o * ∏ g, wg o g (x g)) :
    separatedMoment μ D e reps P c wg =
      ∑ z, WeightedSupport.scalarHom (w z) * groupProduct μ D P z := by
  unfold separatedMoment
  rw [← SubexpSeparation.weighted_separation_equiv_map_weights
    (WeightedSupport.scalarHom (ι := ι)) e reps (group μ D P) w c wg
    (fun o g x y hxy => congrArg (Truncation.canonical μ D (D + μ)) (hP o g x y hxy)) hw]
  rw [Truncation.canonical_sum]
  apply Finset.sum_congr rfl
  intro z hz
  exact Truncation.canonical_scalar_mul μ D (D + μ) (w z) _

omit [Fintype Ω] [DecidableEq G] in
/-- Every canonical product has the actual retained monomial support. -/
theorem groupProduct_support (μ D j r : ℕ) (P : G → Ω → Poly ι R) (z : Ω) :
    (((groupProduct μ D P z).coeff j).coeff r).support ⊆ Moments.retained (D + μ) :=
  Counting.canonical_support μ D (D + μ) j r _

omit [Fintype ι] [Fintype Ω] [DecidableEq G] in
/-- Lemma 4.1, after independently reducing every color group. -/
theorem groupProduct_substitution (μ D : ℕ) (P : G → Ω → Poly ι R)
    (v : Ω → ι → R) (hP : ∀ g z, WeightedSupport.Admissible (P g z))
    (hhigh : ∀ z j, μ ≤ j →
      (Truncation.substX (v z) (∏ g, P g z)).coeff j = 0) (z : Ω) :
    Truncation.evalXU (v z) (groupProduct μ D P z) =
      Truncation.trunc D (Truncation.evalXU (v z) (∏ g, P g z)) :=
  SubexpGlobalPolynomial.truncated_groups_substitution (v z) μ D Finset.univ
    (fun g => P g z) (fun g _ => hP g z) (hhigh z)

/-- Exact multi-color symbolic counting before global interpolation. All
canonical products and separated sums are actual definitions above. -/
theorem separatedJet_eq_sum (μ D : ℕ)
    (e : Ω ≃ Σ o, ∀ g, X o g) (reps : ∀ o g, X o g)
    (P : G → Ω → Poly ι R) (v : Ω → ι → R)
    (c : (ι →₀ ℕ) → O → R) (wg : (ι →₀ ℕ) → ∀ o g, X o g → R)
    (hP : ∀ o g x y, x g = y g → P g (e.symm ⟨o, x⟩) = P g (e.symm ⟨o, y⟩))
    (hw : ∀ a o x, Moments.weight a (v (e.symm ⟨o, x⟩)) = c a o * ∏ g, wg a o g (x g))
    (hPa : ∀ g z, WeightedSupport.Admissible (P g z))
    (hhigh : ∀ z j, μ ≤ j →
      (Truncation.substX (v z) (∏ g, P g z)).coeff j = 0) :
    separatedJet μ D e reps P c wg =
      ∑ z, Truncation.trunc D (Truncation.evalXU (v z) (∏ g, P g z)) := by
  classical
  calc
    separatedJet μ D e reps P c wg =
        ∑ a ∈ Moments.retained (D + μ),
          (Counting.extractX a (∑ z, WeightedSupport.scalarHom (Moments.weight a (v z)) *
            groupProduct μ D P z)).eval 1 := by
      unfold separatedJet
      apply Finset.sum_congr rfl
      intro a ha
      rw [separatedMoment_eq_sum μ D e reps P
        (fun z => Moments.weight a (v z)) (c a) (wg a) hP (hw a)]
    _ = ∑ z, Truncation.evalXU (v z) (groupProduct μ D P z) :=
      Moments.sum_retained_nested_moments_eval_one_eq_sum_evalXU (D + μ)
        (groupProduct μ D P) v (fun z j r => groupProduct_support μ D j r P z)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z hz
      exact groupProduct_substitution μ D P v hPa hhigh z

end Local

section Rows

variable {V E G Ω O R : Type*} {X : O → G → Type*} {σ : E → Type*}
  [CommRing R] [Fintype V] [Fintype E] [Fintype G] [DecidableEq G]
  [Fintype Ω] [Fintype O] [∀ o g, Fintype (X o g)]

/-- The separated jet with each group built from the actual colored factor
polynomials and their incidence-specific polynomial rows. -/
def rowJet (μ D : ℕ) (e : Ω ≃ Σ o, ∀ g, X o g) (reps : ∀ o g, X o g)
    (color : E → G) (table : ∀ e, MvPolynomial (σ e) R)
    (row : ∀ e, σ e → V → Polynomial R) (θ : R) (Rdeg : ℕ)
    (β : Ω → ∀ e, σ e → R)
    (c : (V →₀ ℕ) → O → R) (wg : (V →₀ ℕ) → ∀ o g, X o g → R) : Polynomial R :=
  separatedJet μ D e reps
    (fun g => Counting.rowGroup (SubexpGlobalPolynomial.colorSet color g)
      table row θ Rdeg β) c wg

/-- Local degree, residue-defect, and own-color invariance properties suffice
for the defined separated calculation to recover the true global jet. -/
theorem rowJet_eq (μ D : ℕ) (e : Ω ≃ Σ o, ∀ g, X o g) (reps : ∀ o g, X o g)
    (color : E → G) (table : ∀ e, MvPolynomial (σ e) R)
    (row : ∀ e, σ e → V → Polynomial R) (θ : R) (Rdeg : ℕ)
    (β : Ω → ∀ e, σ e → R) (v : Ω → V → R)
    (c : (V →₀ ℕ) → O → R) (wg : (V →₀ ℕ) → ∀ o g, X o g → R)
    (hβ : ∀ o g x y, x g = y g → ∀ f, color f = g → ∀ i,
      β (e.symm ⟨o, x⟩) f i = β (e.symm ⟨o, y⟩) f i)
    (hw : ∀ a o x, Moments.weight a (v (e.symm ⟨o, x⟩)) = c a o * ∏ g, wg a o g (x g))
    (hrow : ∀ f i w, (row f i w).natDegree ≤ Rdeg)
    (p : R) (hnil : p ^ μ = 0)
    (hdefect : ∀ z f i, p ∣ MvPolynomial.eval (v z)
      (Counting.rowCoefficient (row f i) θ 0) - β z f i) :
    rowJet μ D e reps color table row θ Rdeg β c wg =
      JetCRT.jet θ D (GlobalPolynomial.globalPolynomial table
        (fun z f i => GlobalPolynomial.rowValue (row f i) (v z))) := by
  calc
    rowJet μ D e reps color table row θ Rdeg β c wg =
        ∑ z, Truncation.trunc D (Truncation.evalXU (v z)
          (∏ g, Counting.rowGroup (SubexpGlobalPolynomial.colorSet color g)
            table row θ Rdeg β z)) := by
      apply separatedJet_eq_sum (v := v)
      · intro o g x y hxy
        apply Counting.rowGroup_congr
        intro f hf i
        exact hβ o g x y hxy f ((SubexpGlobalPolynomial.mem_colorSet color g f).mp hf) i
      · exact hw
      · intro g z
        exact Counting.rowGroup_admissible _ table row θ Rdeg β z
      · intro z j hj
        exact SubexpGlobalPolynomial.colored_rowGroup_highU color table row θ Rdeg β
          z (v z) p μ hnil (hdefect z) j hj
    _ = JetCRT.jet θ D (GlobalPolynomial.globalPolynomial table
        (fun z f i => GlobalPolynomial.rowValue (row f i) (v z))) := by
      rw [Counting.jet_eq_trunc]
      exact SubexpGlobalPolynomial.sum_trunc_evalXU_colored_rowGroups D color table row θ
        Rdeg β v hrow

end Rows

section LayoutCounting

variable {p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {V F K R : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
  [Field K] [Fintype K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [CommRing R] {P : Factor.Pattern V F} {c : SubexpLayoutSpec.Parameters p k Δ r tau}
  {L : SubexpLayoutSpec.Layout (E := K) P c}

/-- The actual chosen lift of each incidence row's residue. -/
def layoutBeta (A : SubexpLayoutSpec.LiftedLayout L R) (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (s : CosetInvariance.ResidueSection A.residue) (t : Fin c.Q)
    (x : V → ZMod p) (e : F) (i : {v // v ∈ P.scope e}) : R :=
  (A.liftedRow lift hLift t e i).beta s x

/-- Full symbolic groups indexed by all r colors. -/
def layoutGroup (A : SubexpLayoutSpec.LiftedLayout L R) (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (s : CosetInvariance.ResidueSection A.residue)
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R)
    (t : Fin c.Q) (g : Fin r) : (V → ZMod p) → Poly V R :=
  Counting.rowGroup (SubexpGlobalPolynomial.colorSet (fun e => L.color e t) g)
    table A.row (A.theta t) c.R (layoutBeta A lift hLift s t)

omit [DecidableEq F] [Fintype K] [FiniteDimensional (ZMod p) K] in
/-- The coefficient of U becomes p-divisible under input substitution because
beta is an actual section of the residue map. -/
theorem layoutBeta_defect (A : SubexpLayoutSpec.LiftedLayout L R)
    (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (s : CosetInvariance.ResidueSection A.residue)
    (hker : RingHom.ker A.residue = Ideal.span ({(p : R)} : Set R))
    (t : Fin c.Q) (x : V → ZMod p) (e : F) (i : {v // v ∈ P.scope e}) :
    (p : R) ∣ MvPolynomial.eval (fun w => lift (x w))
      (Counting.rowCoefficient (A.row e i) (A.theta t) 0) - layoutBeta A lift hLift s t x e i := by
  rw [Counting.eval_rowCoefficient_zero]
  exact (A.liftedRow lift hLift t e i).value_sub_beta_dvd s (p : R) hker x

omit [DecidableEq F] [Fintype K] [FiniteDimensional (ZMod p) K] in
/-- The complement-coordinate part of an actual moment weight. -/
def layoutOuterWeight (L : SubexpLayoutSpec.Layout (E := K) P c)
    (lift : ZMod p → R) (t : Fin c.Q) (a : V →₀ ℕ) (o : L.Outer t) : R :=
  ∏ i : ↥((Finset.univ.biUnion (L.support t))ᶜ), lift (o.1 i) ^ a i.val

/-- The part of the moment weight supported on a single color. -/
def layoutInnerWeight (L : SubexpLayoutSpec.Layout (E := K) P c)
    (lift : ZMod p → R) (t : Fin c.Q) (a : V →₀ ℕ)
    (o : L.Outer t) (g : Fin r) (x : L.Inner t o g) : R :=
  ∏ i : L.support t g, lift (x.val i) ^ a i.val

local instance innerFintype (t : Fin c.Q) (o : L.Outer t) (g : Fin r) :
    Fintype (L.Inner t o g) := by
  classical
  unfold SubexpLayoutSpec.Layout.Inner CosetCardinality.CosetFiber
  infer_instance

/-- The separated calculation on the actual outer coordinates and color
cosets of a layout. Its representatives are independent of every moment. -/
def layoutJet (A : SubexpLayoutSpec.LiftedLayout L R) (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (s : CosetInvariance.ResidueSection A.residue)
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R)
    (μ D : ℕ) (t : Fin c.Q) : Polynomial R := by
  classical
  exact rowJet μ D (L.coordinateOuterFiberEquiv t)
    (fun o g => Counting.cosetRepresentative (L.localK t g) (o.2 g))
    (fun e => L.color e t) table A.row (A.theta t) c.R
    (layoutBeta A lift hLift s t)
    (layoutOuterWeight L lift t) (layoutInnerWeight L lift t)

omit [DecidableEq F] [Fintype K] [FiniteDimensional (ZMod p) K] in
/-- Every semantic premise of multicolor separation is supplied by the
actual layout, its lifted rows, and the principal nilpotent residue kernel. -/
theorem layoutJet_eq (A : SubexpLayoutSpec.LiftedLayout L R) (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (s : CosetInvariance.ResidueSection A.residue)
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R)
    (μ D : ℕ) (hnil : (p : R) ^ μ = 0)
    (hker : RingHom.ker A.residue = Ideal.span ({(p : R)} : Set R))
    (t : Fin c.Q) :
    layoutJet A lift hLift s table μ D t =
      JetCRT.jet (A.theta t) D
        (GlobalPolynomial.rowGlobalPolynomial table A.row lift) := by
  classical
  unfold layoutJet
  refine rowJet_eq (V := V) (E := F) (G := Fin r) (Ω := V → ZMod p)
    (O := L.Outer t) (X := L.Inner t) (R := R) μ D
    (L.coordinateOuterFiberEquiv t)
    (fun o g => Counting.cosetRepresentative (L.localK t g) (o.2 g))
    (fun e => L.color e t) table A.row (A.theta t) c.R
    (layoutBeta A lift hLift s t) (fun x w => lift (x w))
    (layoutOuterWeight L lift t) (layoutInnerWeight L lift t)
    ?_ ?_ A.row_degree (p : R) hnil ?_
  · intro o g x y hxy e he i
    change L.color e t = g at he
    subst g
    exact A.beta_reconstruct_eq lift hLift s t e i o hxy
  · intro a o x
    exact SubexpSeparation.momentWeight_of_components (L.support t)
      (L.support_disjoint t) a lift (L.reconstruct t o x) o.1
      (fun g => (x g).val) (L.reconstruct_components t o x).1
      (L.reconstruct_components t o x).2
  · exact fun x e i => layoutBeta_defect A lift hLift s hker t x e i

omit [DecidableEq F] [Fintype K] [FiniteDimensional (ZMod p) K] in
/-- The distinct residue nodes have unit differences in the lifted ring. -/
theorem theta_unit_differences (A : SubexpLayoutSpec.LiftedLayout L R)
    (s : CosetInvariance.ResidueSection A.residue) (μ : ℕ)
    (hnil : (p : R) ^ μ = 0)
    (hker : RingHom.ker A.residue = Ideal.span ({(p : R)} : Set R)) :
    Pairwise (fun i j => IsUnit (A.theta i - A.theta j)) := by
  intro i j hij
  apply NilpotentDefect.isUnit_of_residue_ne_zero A.residue
    (fun z => ⟨s.lift z, s.residue_lift z⟩) (p : R) μ hnil
  · intro z hz
    rw [← Ideal.mem_span_singleton, ← hker]
    exact hz
  · rw [map_sub, A.residue_theta, A.residue_theta]
    intro h
    exact hij (L.node_injective (sub_eq_zero.mp h))

omit [Fintype K] [FiniteDimensional (ZMod p) K] in
/-- Explicit finite geometric correction of each residue-field inverse. -/
def differenceInverse (A : SubexpLayoutSpec.LiftedLayout L R)
    (s : CosetInvariance.ResidueSection A.residue) (μ : ℕ)
    (i j : Fin c.Q) : R :=
  NilpotentDefect.residueInverse A.residue s.lift μ (A.theta i - A.theta j)

omit [DecidableEq F] [Fintype K] [FiniteDimensional (ZMod p) K] in
theorem differenceInverse_mul (A : SubexpLayoutSpec.LiftedLayout L R)
    (s : CosetInvariance.ResidueSection A.residue) (μ : ℕ)
    (hnil : (p : R) ^ μ = 0)
    (hker : RingHom.ker A.residue = Ideal.span ({(p : R)} : Set R))
    (i j : Fin c.Q) (hij : i ≠ j) :
    differenceInverse A s μ i j * (A.theta i - A.theta j) = 1 := by
  rw [mul_comm]
  apply NilpotentDefect.mul_residueInverse A.residue s.lift s.residue_lift (p : R) μ hnil
  · intro z hz
    rw [← Ideal.mem_span_singleton, ← hker]
    exact hz
  · rw [map_sub, A.residue_theta, A.residue_theta]
    intro h
    exact hij (L.node_injective (sub_eq_zero.mp h))

/-- Explicit finite geometric CRT applied to the defined separated jets.
No inverse or Bezout certificates are supplied by the caller. -/
def explicitReconstruction (A : SubexpLayoutSpec.LiftedLayout L R) (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (s : CosetInvariance.ResidueSection A.residue)
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R)
    (μ D : ℕ) : Polynomial R :=
  TruncatedInverse.reconstruct A.theta D
    (TruncatedInverse.constantInverse D (differenceInverse A s μ))
    (layoutJet A lift hLift s table μ D)

omit [DecidableEq F] [Fintype K] [FiniteDimensional (ZMod p) K] in
theorem explicitReconstruction_eq (A : SubexpLayoutSpec.LiftedLayout L R)
    (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (s : CosetInvariance.ResidueSection A.residue)
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R)
    (μ D : ℕ) (hD : 0 < D) (hnil : (p : R) ^ μ = 0)
    (hker : RingHom.ker A.residue = Ideal.span ({(p : R)} : Set R))
    (hdegree : (GlobalPolynomial.rowGlobalPolynomial table A.row lift).natDegree < c.Q * D) :
    explicitReconstruction A lift hLift s table μ D =
      GlobalPolynomial.rowGlobalPolynomial table A.row lift := by
  nontriviality R
  let _ : Nonempty (Fin c.Q) := ⟨⟨0, c.toConstants.Q_pos⟩⟩
  apply TruncatedInverse.reconstruct_eq A.theta D hD
    (theta_unit_differences A s μ hnil hker)
  · exact TruncatedInverse.constantInverse_correct A.theta D _
      (differenceInverse_mul A s μ hnil hker)
  · simpa using hdegree
  · intro t
    rw [layoutJet_eq A lift hLift s table μ D hnil hker t, Counting.jet_eq_trunc]
    exact TruncatedInverse.trunc_idempotent D _

end LayoutCounting

section InterpolatedCounting

variable {p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {V F K R : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
  [Field K] [Fintype K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [CommRing R] (S : Factor.System V F (ZMod p)) {c : SubexpLayoutSpec.Parameters p k Δ r tau}
  {L : SubexpLayoutSpec.Layout (E := K) S.toPattern c}

omit [Fintype K] [FiniteDimensional (ZMod p) K] in
omit [DecidableEq F] in
/-- The degree budget is uniform in the number of colors: colors do not
increase the degree of the actual global polynomial. -/
theorem interpolated_degree_lt (A : SubexpLayoutSpec.LiftedLayout L R)
    (lift : ZMod p → R) (hu : TableInterpolation.UnitDifferences lift)
    (hD : 0 < Fintype.card V) :
    (GlobalPolynomial.interpolatedGlobalPolynomial S lift hu A.row).natDegree <
      c.Q * Fintype.card V := by
  have hm : Fintype.card F ≤ Δ * Fintype.card V := by
    apply Incidence.card_factors_le S.scope Δ L.bounded.nonempty_scope
    intro w
    exact L.bounded.incidence_le w
  have hd := GlobalPolynomial.natDegree_interpolatedGlobalPolynomial_le S lift hu A.row
    k c.R L.bounded.arity_le A.row_degree
  calc
    (GlobalPolynomial.interpolatedGlobalPolynomial S lift hu A.row).natDegree ≤
        Fintype.card F * k * (p - 1) * c.R := by simpa only [ZMod.card] using hd
    _ ≤ (Δ * Fintype.card V) * k * (p - 1) * c.R :=
      Nat.mul_le_mul_right c.R (Nat.mul_le_mul_right (p - 1) (Nat.mul_le_mul_right k hm))
    _ = Fintype.card V * (Δ * k * (p - 1) * c.R) := by ac_rfl
    _ < Fintype.card V * c.Q := Nat.mul_lt_mul_of_pos_left c.degree_budget hD
    _ = c.Q * Fintype.card V := Nat.mul_comm _ _

/-- Evaluate the explicit reconstruction of the interpolated factor tables
at the selector origin. This is a defined calculation, not a count oracle. -/
def explicitRecoveredValue (A : SubexpLayoutSpec.LiftedLayout L R) (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (hu : TableInterpolation.UnitDifferences lift)
    (s : CosetInvariance.ResidueSection A.residue) (μ : ℕ) : R :=
  (explicitReconstruction A lift hLift s (GlobalPolynomial.interpolatedTable S lift hu)
    μ (Fintype.card V)).eval 0

omit [DecidableEq F] [Fintype K] [FiniteDimensional (ZMod p) K] in
theorem explicitRecoveredValue_eq_count (A : SubexpLayoutSpec.LiftedLayout L R)
    (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (hu : TableInterpolation.UnitDifferences lift)
    (s : CosetInvariance.ResidueSection A.residue)
    (μ : ℕ) (hnil : (p : R) ^ μ = 0)
    (hker : RingHom.ker A.residue = Ideal.span ({(p : R)} : Set R))
    (hD : 0 < Fintype.card V) :
    explicitRecoveredValue S A lift hLift hu s μ = (Factor.count S : R) := by
  unfold explicitRecoveredValue
  rw [explicitReconstruction_eq A lift hLift s _ μ (Fintype.card V) hD hnil hker
    (interpolated_degree_lt S A lift hu hD)]
  exact GlobalPolynomial.eval_zero_interpolatedGlobalPolynomial S lift hu A.row A.row_zero

end InterpolatedCounting

section ActualCounting

variable {p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
  (S : Factor.System V F (ZMod p)) {c : SubexpLayoutSpec.Parameters p k Δ r tau}
  (L : SubexpLayoutSpec.Layout (E := FiniteField.E p c.h) S.toPattern c)

/-- Lift every node and incidence row of the multicolor layout into the
actual monic quotient with this same residue field. -/
def actualLiftedLayout (μ : ℕ) (hμ : 0 < μ) :
    SubexpLayoutSpec.LiftedLayout L (ActualLiftRing.Ring p c.h μ) :=
  SubexpLayoutSpec.LiftedLayout.ofSurjective L
    (ActualLiftRing.rho p c.h μ hμ) (ActualLiftRing.rho_surjective p c.h μ hμ)

omit [DecidableEq F] in
@[simp] theorem actualLiftedLayout_residue (μ : ℕ) (hμ : 0 < μ) :
    (actualLiftedLayout S L μ hμ).residue = ActualLiftRing.rho p c.h μ hμ := rfl

/-- The fully instantiated output of the actual multicolor separated
calculation and finite geometric CRT, in the prime-power ring with mu=D+1. -/
def actualRingValue : ActualLiftRing.Ring p c.h (Fintype.card V + 1) :=
  explicitRecoveredValue S
    (actualLiftedLayout S L (Fintype.card V + 1) (Nat.succ_pos _))
    (ActualLiftRing.coordinateLift p c.h (Fintype.card V + 1))
    (ActualLiftRing.rho_coordinateLift p c.h (Fintype.card V + 1) (Nat.succ_pos _))
    (ActualLiftRing.coordinateLift_unitDifferences p c.h (Fintype.card V + 1))
    (ActualLiftRing.residueSection p c.h (Fintype.card V + 1) (Nat.succ_pos _))
    (Fintype.card V + 1)

omit [DecidableEq F] in
/-- All ring, lift, kernel, nilpotence, inverse, and local-separation conditions
have been discharged. The layout and positive dimension are the only inputs. -/
theorem actualRingValue_eq_count (hD : 0 < Fintype.card V) :
    actualRingValue S L =
      (Factor.count S : ActualLiftRing.Ring p c.h (Fintype.card V + 1)) := by
  unfold actualRingValue
  exact explicitRecoveredValue_eq_count S
    (actualLiftedLayout S L (Fintype.card V + 1) (Nat.succ_pos _))
    (ActualLiftRing.coordinateLift p c.h (Fintype.card V + 1))
    (ActualLiftRing.rho_coordinateLift p c.h (Fintype.card V + 1) (Nat.succ_pos _))
    (ActualLiftRing.coordinateLift_unitDifferences p c.h (Fintype.card V + 1))
    (ActualLiftRing.residueSection p c.h (Fintype.card V + 1) (Nat.succ_pos _))
    (Fintype.card V + 1)
    (ActualLiftRing.prime_power_zero p c.h (Fintype.card V + 1))
    (ActualLiftRing.rho_ker p c.h (Fintype.card V + 1) (Nat.succ_pos _)) hD

/-- Decode the actual output using its canonical constant coefficient.
No call to the target factor count occurs in this definition. -/
def actualCount : ℕ :=
  ActualLiftRing.decodeCount p c.h (Fintype.card V + 1) (Nat.succ_pos _)
    (actualRingValue S L)

omit [DecidableEq F] in
/-- Exact natural-number counting from the multicolor interpolation layout,
uniformly in the number of colors and all field parameters. -/
theorem actualCount_eq_count (hD : 0 < Fintype.card V) :
    actualCount S L = Factor.count S := by
  rw [actualCount, actualRingValue_eq_count S L hD]
  exact ActualLiftRing.decodeCount_natCast p c.h (Fintype.card V + 1) (Nat.succ_pos _)
    (Nat.ne_of_gt c.h_pos) (Factor.count S) (Counting.factor_count_lt_prime_power S)

omit [DecidableEq F] in
/-- Positivity of the recovered integer has the intended assignment semantics.
Executable refinement and running time are separate from this identity. -/
theorem actualCount_pos_iff (hD : 0 < Fintype.card V) :
    0 < actualCount S L ↔ ∃ x : V → ZMod p, Factor.Satisfies S x := by
  rw [actualCount_eq_count S L hD]
  exact Factor.count_pos_iff S

end ActualCounting

section SelectedQuarticCounting

variable {p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
  (S : Factor.System V F (ZMod p)) {c : SubexpLayoutSpec.Parameters p k Δ r tau}
  (L : SubexpLayoutSpec.Layout (E := SubexpActualRing.E p) S.toPattern c)

/-- The multicolor layout lifted into the quotient by the exact quartic
coefficients returned by the executable field construction, using finite
coefficientwise lifting of every row. -/
def selectedLiftedLayout (μ : ℕ) (hμ : 0 < μ) :
    SubexpLayoutSpec.LiftedLayout L (SubexpActualRing.Ring p μ) :=
  SubexpExplicitLift.explicitLiftedLayout L μ hμ

omit [DecidableEq F] in
@[simp] theorem selectedLiftedLayout_residue (μ : ℕ) (hμ : 0 < μ) :
    (selectedLiftedLayout S L μ hμ).residue = SubexpActualRing.rho p μ hμ := rfl

/-- Exact-ring output using the selected quartic and its integer coefficient
lifts, with the same separated moments and finite geometric reconstruction. -/
def selectedRingValue : SubexpActualRing.Ring p (Fintype.card V + 1) :=
  explicitRecoveredValue S
    (selectedLiftedLayout S L (Fintype.card V + 1) (Nat.succ_pos _))
    (SubexpActualRing.coordinateLift p (Fintype.card V + 1))
    (SubexpActualRing.rho_coordinateLift p (Fintype.card V + 1) (Nat.succ_pos _))
    (SubexpActualRing.coordinateLift_unitDifferences p (Fintype.card V + 1))
    (SubexpActualRing.residueSection p (Fintype.card V + 1) (Nat.succ_pos _))
    (Fintype.card V + 1)

omit [DecidableEq F] in
theorem selectedRingValue_eq_count (hD : 0 < Fintype.card V) :
    selectedRingValue S L =
      (Factor.count S : SubexpActualRing.Ring p (Fintype.card V + 1)) := by
  unfold selectedRingValue
  exact explicitRecoveredValue_eq_count S
    (selectedLiftedLayout S L (Fintype.card V + 1) (Nat.succ_pos _))
    (SubexpActualRing.coordinateLift p (Fintype.card V + 1))
    (SubexpActualRing.rho_coordinateLift p (Fintype.card V + 1) (Nat.succ_pos _))
    (SubexpActualRing.coordinateLift_unitDifferences p (Fintype.card V + 1))
    (SubexpActualRing.residueSection p (Fintype.card V + 1) (Nat.succ_pos _))
    (Fintype.card V + 1)
    (SubexpActualRing.prime_power_zero p (Fintype.card V + 1))
    (SubexpActualRing.rho_ker p (Fintype.card V + 1) (Nat.succ_pos _)) hD

/-- Decode the actual multicolor output in the selected-quartic quotient. -/
def selectedCount : ℕ :=
  SubexpActualRing.decodeCount p (Fintype.card V + 1) (Nat.succ_pos _)
    (selectedRingValue S L)

omit [DecidableEq F] in
/-- The exact natural count using the same quartic as the executable ring
backend. No field identification or count equality is an input. -/
theorem selectedCount_eq_count (hD : 0 < Fintype.card V) :
    selectedCount S L = Factor.count S := by
  rw [selectedCount, selectedRingValue_eq_count S L hD]
  exact SubexpActualRing.decodeCount_natCast p (Fintype.card V + 1) (Nat.succ_pos _)
    (Factor.count S) (Counting.factor_count_lt_prime_power S)

omit [DecidableEq F] in
theorem selectedCount_pos_iff (hD : 0 < Fintype.card V) :
    0 < selectedCount S L ↔ ∃ x : V → ZMod p, Factor.Satisfies S x := by
  rw [selectedCount_eq_count S L hD]
  exact Factor.count_pos_iff S

end SelectedQuarticCounting



end

end SubexponentialSAT.SubexpCounting

end OAI.Algorithms
