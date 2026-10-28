import Mathlib
import OAI.AlgebraicGeometry.ComplexMultiplication.HeckePolynomial

/-! # Frobenius Slope Comparison Newton -/

namespace OAI.NumberTheory.PadicHodge.FrobeniusSlopeComparisonNewton

section

/-!
# FrobeniusSlope: forced Frobenius eigenvalue and slope, conditional on the graph inputs

The geometric interfaces in GeometricComparison, Completion and IntegralComparison are still specification schemas.
This proof uses the concrete cohomological consequences already exposed by
Statements/FrobeniusSlope.lean, with explicit names recording their provenance:

* `hRadialDilation`: the complex absolute value of e is one, obtained from RadialDilation's
 algebraic-unit-circle conclusion (equation (4)).
* `hCubicRelation`: the specialized cubic after its transport to contravariant H¹.
* `hCentralConstraint_central` and `hCentralConstraint_satake`: the central root-of-unity relation
 and the three generalized Hecke eigenvalues after absorbing C₀.
* `hGeometricComparison_Completion_IntegralComparison`: the weight-one absolute value for the transported
 crystalline eigenvalues, as supplied by comparison and the Weil theorem.
* `hCommuting`: the full Commuting conclusion for the family consisting of Frobenius
 and the three Hecke operators. Its proposition is copied below, with
 exactly the generalized eigenspace definition from that specification.

No statement stub is imported or used as a fact. Only the spanning and
polynomial-descent clauses of Commuting are needed; its common triangular basis,
finiteness and independence clauses are unused. Weak admissibility and the
filtered-dimension conclusions of GeometricComparison are unnecessary for this result.
The geometric realization remains the same explicit interface boundary as
in the target specification; no additional geometric assumption is added.

The target's non-parsing identifiers `j∞`, `hr∞`, `he∞` and `λ` are spelled
`jC`, `hrC`, `hRadialDilation` and `μ` here. This is only a syntactic correction.
The committed statement specification is left unchanged. The slope uses
an additive valuation with ν(q) = 1 and the supplied finite value s = ν(ι e).
-/

open _root_.Module

/-- The generalized eigenspace used in the Commuting specification. -/
def jointGenEigenspace {L V I : Type*} [Field L]
    [AddCommGroup V] [Module L V]
    (T : I → Module.End L V) (χ : I → L) : Submodule L V :=
  ⨅ i, (T i).genEigenspace (χ i) ⊤

/-- The full conclusion of Commuting, specialized to the four operators needed here.
This is an input proposition, not an axiom or an invocation of its statement stub. -/
def CommutingInput (L V : Type*) [Field L] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] : Prop :=
  ∀ (T : Fin 4 → Module.End L V),
    (∀ i j, Commute (T i) (T j)) →
    ∃ ev : MvPolynomial (Fin 4) L →ₐ[L] Module.End L V,
      (∀ i, ev (MvPolynomial.X i) = T i) ∧
      (∃ b : Module.Basis (Fin (Module.finrank L V)) L V,
        ∀ i (r c : Fin (Module.finrank L V)),
          c < r → b.repr (T i (b c)) r = 0) ∧
      Set.Finite {χ : Fin 4 → L | jointGenEigenspace T χ ≠ ⊥} ∧
      iSupIndep (fun χ : Fin 4 → L => jointGenEigenspace T χ) ∧
      (⨆ χ : Fin 4 → L, jointGenEigenspace T χ) = ⊤ ∧
      (∀ (χ : Fin 4 → L) (p : MvPolynomial (Fin 4) L),
        jointGenEigenspace T χ ≠ ⊥ →
        ev p = 0 → MvPolynomial.eval χ p = 0)

lemma generalized_eigenvalue_unique
    {L V : Type*} [Field L] [AddCommGroup V] [Module L V]
    (f : Module.End L V) (a μ : L)
    (htop : f.genEigenspace a ⊤ = ⊤)
    (hμ : f.genEigenspace μ ⊤ ≠ ⊥) : μ = a := by
  by_contra hne
  have hd := f.disjoint_genEigenspace hne ⊤ ⊤
  rw [htop, disjoint_top] at hd
  exact hμ hd

lemma central_norm_one
    {K : Type*} [Field K] (j : K →+* ℂ) (b e : K)
    (he : ‖j e‖ = 1)
    (hcentral : ∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1) :
    ‖j b‖ = 1 := by
  obtain ⟨n, hn, hc⟩ := hcentral
  have hc' := congrArg (fun x : K => ‖j x‖) hc
  simp only [map_pow, map_mul, norm_pow, norm_mul, map_one, norm_one, he,
    mul_one] at hc'
  have hb3 : ‖j b‖ ^ 3 = 1 :=
    (pow_left_inj₀ (by positivity) zero_le_one hn.ne').mp (by simpa using hc')
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one (by omega : (3 : ℕ) ≠ 0)).mp
    (by simpa using hb3)

lemma valuation_of_forced_root
    {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L]
    (q : ℕ) (hq : q.Prime) (ι : K →+* L) (r b e : K)
    (hr : r ^ 2 = (q : K))
    (hcentral : ∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1)
    (ν : AddValuation L (WithTop ℚ))
    (hνq : ν (q : L) = (1 : WithTop ℚ))
    (s : ℚ) (hνe : ν (ι e) = (s : WithTop ℚ)) :
    ν (ι (b * r)) = ((1 / 2 - s / 3 : ℚ) : WithTop ℚ) := by
  obtain ⟨n, hn, hc⟩ := hcentral
  have hb : b ≠ 0 := by
    intro hb
    simp [hb, hn.ne'] at hc
  have hr0 : r ≠ 0 := by
    intro hz
    have hq0 : (q : K) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
    exact hq0 (by simpa [hz] using hr.symm)
  obtain ⟨vb, hvb⟩ := WithTop.ne_top_iff_exists.mp
    ((ν.ne_top_iff).mpr ((map_ne_zero ι).mpr hb))
  obtain ⟨vr, hvr⟩ := WithTop.ne_top_iff_exists.mp
    ((ν.ne_top_iff).mpr ((map_ne_zero ι).mpr hr0))
  have hbc := congrArg (fun x : K => ν (ι x)) hc
  simp only [map_pow, map_mul, map_one, ν.map_pow, ν.map_mul, ν.map_one,
    ← hvb, hνe] at hbc
  have hrc := congrArg (fun x : K => ν (ι x)) hr
  simp only [map_pow, map_natCast, ν.map_pow, ← hvr, hνq] at hrc
  have hbcQ : (n : ℚ) * (3 * vb + s) = 0 := by
    exact_mod_cast (show (n : ℚ) • (3 • vb + s) = 0 from by exact_mod_cast hbc)
  have hrcQ : 2 * vr = (1 : ℚ) := by
    simpa using (show (2 : ℕ) • vr = (1 : ℚ) from by exact_mod_cast hrc)
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hbQ : 3 * vb + s = 0 := (mul_eq_zero.mp hbcQ).resolve_left hnQ
  rw [map_mul, ν.map_mul, ← hvb, ← hvr, ← WithTop.coe_add]
  congr 1
  linarith

lemma select_middle_root
    {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L]
    (q : ℕ) (hq : q.Prime) (jC : K →+* ℂ) (ι : K →+* L)
    (r b e : K) (hr : r ^ 2 = (q : K))
    (hrC : jC r = (Real.sqrt (q : ℝ) : ℂ))
    (heC : ‖jC e‖ = 1)
    (hcentral : ∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1)
    (μ : L)
    (hcubic : μ ^ 3 - ι ((q : K) * b * (r + r⁻¹ + e)) * μ ^ 2 +
      (q : L) * ι ((q : K) * b ^ 2 * (r * r⁻¹ + r * e + r⁻¹ * e)) * μ -
      (q : L) ^ 3 * ι (b ^ 3 * e) = 0)
    (hWeil : ∀ a : K, μ = ι a → ‖jC a‖ = Real.sqrt (q : ℝ)) :
    μ = ι (b * r) := by
  have hr0 : r ≠ 0 := by
    intro hz
    have hq0 : (q : K) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
    exact hq0 (by simpa [hz] using hr.symm)
  have hir0 : ι r ≠ 0 := (map_ne_zero ι).mpr hr0
  have hroot :
      (μ - ι ((q : K) * b * r)) *
      (μ - ι ((q : K) * b * r⁻¹)) *
      (μ - ι ((q : K) * b * e)) = 0 := by
    simp only [map_mul, map_add, map_pow, map_inv₀, map_natCast] at hcubic ⊢
    rw [← AlgebraicGeometry.ComplexMultiplication.HeckePolynomial.CM.hecke_cubic_factorization]
    simp only [mul_inv_cancel₀ hir0, one_mul] at hcubic ⊢
    linear_combination hcubic
  obtain ⟨a, hμ, ha⟩ : ∃ a : K, μ = ι a ∧
      (a = (q : K) * b * r ∨ a = (q : K) * b * r⁻¹ ∨
        a = (q : K) * b * e) := by
    rcases mul_eq_zero.mp hroot with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact ⟨_, sub_eq_zero.mp h, Or.inl rfl⟩
      · exact ⟨_, sub_eq_zero.mp h, Or.inr (Or.inl rfl)⟩
    · exact ⟨_, sub_eq_zero.mp h, Or.inr (Or.inr rfl)⟩
  have habs : ‖jC b‖ = 1 := central_norm_one jC b e heC hcentral
  have hforce : jC a = jC (b * r) := by
    rw [map_mul, hrC]
    apply AlgebraicGeometry.ComplexMultiplication.HeckePolynomial.CM.weil_norm_selects_middle_root
      (q : ℝ) (by exact_mod_cast hq.one_lt) (jC b) (jC e) (jC a)
      habs heC (hWeil a hμ)
    rcases ha with rfl | rfl | rfl <;>
      simp [map_mul, map_inv₀, map_natCast, hrC, div_eq_mul_inv]
  exact hμ.trans (congrArg ι (jC.injective hforce))

/-- Conditional FrobeniusSlope, with the same natural hypotheses as its specification.
The source of each geometric input is named at its point of use. -/
theorem forced_frobenius_eigenvalue_and_slope
    {K L V : Type*}
    [Field K] [CharZero K]
    [Field L] [CharZero L] [IsAlgClosed L]
    [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] [Nontrivial V]
    (q : ℕ) (hq : q.Prime)
    (jC : K →+* ℂ) (ι : K →+* L)
    (r b e : K)
    (hr : r ^ 2 = (q : K))
    (hrC : jC r = (Real.sqrt (q : ℝ) : ℂ))
    (hRadialDilation : ‖jC e‖ = 1)
    (hCentralConstraint_central : ∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1)
    (Φ : Module.End L V)
    (T : Fin 3 → Module.End L V)
    (hcomm : ∀ i j, Commute (T i) (T j))
    (hΦcomm : ∀ i, Commute Φ (T i))
    (hCubicRelation :
      Φ ^ 3 - T 0 * Φ ^ 2 +
        q • (T 1 * Φ) - (q ^ 3) • T 2 = 0)
    (hCentralConstraint_satake :
      ∀ i : Fin 3,
        (T i).genEigenspace
          (ι ((![(q : K) * b * (r + r⁻¹ + e),
            (q : K) * b ^ 2 * (r * r⁻¹ + r * e + r⁻¹ * e),
            b ^ 3 * e] : Fin 3 → K) i)) ⊤ = ⊤)
    (hGeometricComparison_Completion_IntegralComparison :
      ∀ a : K, Φ.HasEigenvalue (ι a) →
        ‖jC a‖ = Real.sqrt (q : ℝ))
    (hCommuting : CommutingInput L V)
    (ν : AddValuation L (WithTop ℚ))
    (hνq : ν (q : L) = (1 : WithTop ℚ))
    (s : ℚ)
    (hνe : ν (ι e) = (s : WithTop ℚ)) :
    Φ.genEigenspace (ι (b * r)) ⊤ = ⊤ ∧
      ∀ μ : L, Φ.HasEigenvalue μ →
        μ = ι (b * r) ∧
        ν μ = ((1 / 2 - s / 3 : ℚ) : WithTop ℚ) := by
  let A : Fin 4 → Module.End L V := Fin.cases Φ T
  have hAcomm : ∀ i j, Commute (A i) (A j) := by
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · exact Fin.cases (Commute.refl Φ) (fun j => hΦcomm j) j
    · exact Fin.cases (hΦcomm i).symm (fun j => hcomm i j) j
  obtain ⟨ev, hev, _htriang, _hfinite, _hindep, hspan, hdescend⟩ := hCommuting A hAcomm
  let p : MvPolynomial (Fin 4) L :=
    MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 * MvPolynomial.X 0 ^ 2 +
      q • (MvPolynomial.X 2 * MvPolynomial.X 0) -
      (q ^ 3) • MvPolynomial.X 3
  have hep : ev p = 0 := by
    simp only [p, map_sub, map_add, map_mul, map_pow, map_nsmul, hev]
    change Φ ^ 3 - T 0 * Φ ^ 2 + q • (T 1 * Φ) - (q ^ 3) • T 2 = 0
    exact hCubicRelation
  have hforce : ∀ χ : Fin 4 → L, jointGenEigenspace A χ ≠ ⊥ →
      χ 0 = ι (b * r) := by
    intro χ hχ
    have hnonzero (i : Fin 4) : (A i).genEigenspace (χ i) ⊤ ≠ ⊥ := by
      intro hz
      apply hχ
      apply le_antisymm _ bot_le
      exact (iInf_le (fun j => (A j).genEigenspace (χ j) ⊤) i).trans_eq hz
    have hcoeff (i : Fin 3) : χ i.succ =
        ι ((![(q : K) * b * (r + r⁻¹ + e),
          (q : K) * b ^ 2 * (r * r⁻¹ + r * e + r⁻¹ * e),
          b ^ 3 * e] : Fin 3 → K) i) := by
      exact generalized_eigenvalue_unique (T i) _ _ (hCentralConstraint_satake i) (hnonzero i.succ)
    have hχ0 : Φ.HasEigenvalue (χ 0) :=
      Module.End.HasUnifEigenvalue.lt zero_lt_one (hnonzero 0)
    have hcubic := hdescend χ p hχ hep
    simp only [p, map_sub, map_add, map_mul, map_pow, map_nsmul,
      MvPolynomial.eval_X] at hcubic
    have h1 := hcoeff 0
    have h2 := hcoeff 1
    have h3 := hcoeff 2
    change χ 1 = ι ((q : K) * b * (r + r⁻¹ + e)) at h1
    change χ 2 = ι ((q : K) * b ^ 2 * (r * r⁻¹ + r * e + r⁻¹ * e)) at h2
    change χ 3 = ι (b ^ 3 * e) at h3
    rw [h1, h2, h3] at hcubic
    apply select_middle_root q hq jC ι r b e hr hrC hRadialDilation hCentralConstraint_central (χ 0)
    · simpa only [nsmul_eq_mul, Nat.cast_pow, mul_assoc] using hcubic
    · intro a ha
      exact hGeometricComparison_Completion_IntegralComparison a (ha ▸ hχ0)
  have htop : Φ.genEigenspace (ι (b * r)) ⊤ = ⊤ := by
    apply top_unique
    rw [← hspan]
    refine iSup_le fun χ => ?_
    by_cases hχ : jointGenEigenspace A χ = ⊥
    · rw [hχ]
      exact bot_le
    · have hf := hforce χ hχ
      have hle := iInf_le (fun j => (A j).genEigenspace (χ j) ⊤) 0
      change jointGenEigenspace A χ ≤ Φ.genEigenspace (χ 0) ⊤ at hle
      rw [hf] at hle
      exact hle
  refine ⟨htop, ?_⟩
  intro μ hμ
  have hμtop : Φ.genEigenspace μ ⊤ ≠ ⊥ :=
    Module.End.HasUnifEigenvalue.le le_top hμ
  have heq := generalized_eigenvalue_unique Φ (ι (b * r)) μ htop hμtop
  refine ⟨heq, ?_⟩
  rw [heq]
  exact valuation_of_forced_root q hq ι r b e hr hCentralConstraint_central ν hνq s hνe

end

noncomputable section

open scoped TensorProduct
open _root_.Module _root_.Polynomial

/-- An injective intertwiner carries eigenvalues to the ambient operator. -/
lemma eigenvalue_of_injective_intertwiner
    {L U V : Type*} [Field L] [AddCommGroup U] [Module L U]
    [AddCommGroup V] [Module L V]
    (f : Module.End L U) (g : Module.End L V) (j : U →ₗ[L] V)
    (hj : Function.Injective j) (hfg : j.comp f = g.comp j)
    {a : L} (ha : f.HasEigenvalue a) : g.HasEigenvalue a := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp ha
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := j x)
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · have he := congrArg (fun k : U →ₗ[L] V => k x) hfg
    simpa only [LinearMap.comp_apply, Module.End.mem_eigenspace_iff.mp hx,
      map_smul] using he.symm
  · exact fun h => hx0 (hj (h.trans j.map_zero.symm))

/-- Weight bounds descend to any invariant subspace and then to its
scalar extension; the invariant-subspace inclusion is the actual map. -/
lemma weights_on_baseChanged_subspace
    {B L Ω K D : Type*} [Field B] [Field L] [Field Ω] [Field K]
    [CharZero B] [CharZero L] [CharZero Ω] [CharZero K]
    [Algebra B L] [Algebra L Ω]
    [AddCommGroup D] [Module B D] [FiniteDimensional B D]
    (g : Module.End B D) (W : Polynomial ℤ)
    (hchar : g.charpoly = W.map (Int.castRingHom B))
    (q : ℕ) (hweight : ∀ z : ℂ, Polynomial.aeval z W = 0 →
      ‖z‖ = Real.sqrt (q : ℝ))
    (S : Submodule L (L ⊗[B] D)) (f : Module.End L S)
    (hinclude : ∀ x : S, (f x : L ⊗[B] D) = g.baseChange L (x : L ⊗[B] D))
    (jC : K →+* ℂ) (ι : K →+* Ω) (a : K)
    (ha : Module.End.HasEigenvalue (f.baseChange Ω) (ι a)) :
    ‖jC a‖ = Real.sqrt (q : ℝ) := by
  have hlin : S.subtype.comp f = (g.baseChange L).comp S.subtype :=
    LinearMap.ext hinclude
  have hlin' : (S.subtype.baseChange Ω).comp (f.baseChange Ω) =
      ((g.baseChange L).baseChange Ω).comp (S.subtype.baseChange Ω) := by
    simpa only [LinearMap.baseChange_comp] using
      congrArg (fun k : S →ₗ[L] L ⊗[B] D => k.baseChange Ω) hlin
  have hj : Function.Injective (S.subtype.baseChange Ω) :=
    Module.Flat.lTensor_preserves_injective_linearMap S.subtype S.injective_subtype
  have hbig := eigenvalue_of_injective_intertwiner _ _ _ hj hlin' ha
  have hc : ((g.baseChange L).baseChange Ω).charpoly = W.map (Int.castRingHom Ω) := by
    rw [LinearMap.charpoly_baseChange, LinearMap.charpoly_baseChange, hchar]
    ext i
    simp
  have hroot := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mp hbig
  rw [hc] at hroot
  have haK : Polynomial.aeval a W = 0 := by
    apply ι.injective
    simpa [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def,
      Polynomial.eval₂_at_apply] using hroot
  apply hweight
  have hz := congrArg jC haK
  simpa [Polynomial.aeval_def, Polynomial.eval₂_at_apply] using hz

/-- A pure eigenvalue determines the determinant, including its multiplicity. -/
lemma determinant_of_only_eigenvalue
    {Ω U : Type*} [Field Ω] [IsAlgClosed Ω]
    [AddCommGroup U] [Module Ω U] [FiniteDimensional Ω U]
    (f : Module.End Ω U) (a : Ω)
    (h : ∀ μ, f.HasEigenvalue μ → μ = a) :
    LinearMap.det f = a ^ Module.finrank Ω U := by
  classical
  have hs := IsAlgClosed.splits f.charpoly
  have hr : f.charpoly.roots = Multiset.replicate f.charpoly.roots.card a := by
    apply Multiset.eq_replicate_card.mpr
    intro μ hμ
    exact h μ ((Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mpr
      ((Polynomial.mem_roots f.charpoly_monic.ne_zero).mp hμ))
  rw [Module.End.det_eq_prod_roots_charpoly_of_splits hs, hr, Multiset.prod_replicate]
  rw [← hs.natDegree_eq_card_roots, LinearMap.charpoly_natDegree]

/-- Newton number over the coefficient field, computed from the genuine
Frobenius determinant. No value is assigned to a zero determinant. -/
def coefficientNewton
    {L Ω U : Type*} [Field L] [Field Ω] [Algebra L Ω]
    [AddCommGroup U] [Module L U] [FiniteDimensional L U]
    (ν : AddValuation Ω (WithTop ℚ)) (f : U ≃ₗ[L] U) : ℚ :=
  (ν (algebraMap L Ω (LinearMap.det f.toLinearMap))).untop
    (ν.ne_top_iff.mpr ((map_ne_zero (algebraMap L Ω)).mpr f.isUnit_det'.ne_zero))

/-- The existing numerical FrobeniusSlope proof applies to a scalar-extended genuine
Frobenius equivalence, and determines its coefficient-field determinant. -/
theorem newton_from_weights
    {K L Ω U : Type*} [Field K] [CharZero K]
    [Field L] [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Algebra L Ω]
    [AddCommGroup U] [Module L U] [FiniteDimensional L U]
    (q : ℕ) (hq : q.Prime) (jC : K →+* ℂ) (ι : K →+* Ω)
    (f : U ≃ₗ[L] U)
    (hweight : ∀ a : K, Module.End.HasEigenvalue (f.toLinearMap.baseChange Ω) (ι a) →
      ‖jC a‖ = Real.sqrt (q : ℝ))
    (r b e : K) (hr : r ^ 2 = (q : K))
    (hrC : jC r = (Real.sqrt (q : ℝ) : ℂ))
    (hRadialDilation : ‖jC e‖ = 1)
    (hCentralConstraint_central : ∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1)
    (T : Fin 3 → Module.End Ω (Ω ⊗[L] U))
    (hcomm : ∀ i j, Commute (T i) (T j))
    (hΦcomm : ∀ i, Commute (f.toLinearMap.baseChange Ω) (T i))
    (hCubicRelation :
      (f.toLinearMap.baseChange Ω) ^ 3 - T 0 * (f.toLinearMap.baseChange Ω) ^ 2 +
        q • (T 1 * (f.toLinearMap.baseChange Ω)) - (q ^ 3) • T 2 = 0)
    (hCentralConstraint_satake : ∀ i : Fin 3,
      (T i).genEigenspace
        (ι ((![(q : K) * b * (r + r⁻¹ + e),
          (q : K) * b ^ 2 * (r * r⁻¹ + r * e + r⁻¹ * e),
          b ^ 3 * e] : Fin 3 → K) i)) ⊤ = ⊤)
    (hCommuting : CommutingInput Ω (Ω ⊗[L] U))
    (ν : AddValuation Ω (WithTop ℚ)) (hνq : ν (q : Ω) = 1)
    (s : ℚ) (hνe : ν (ι e) = (s : WithTop ℚ)) :
    Module.End.genEigenspace (f.toLinearMap.baseChange Ω) (ι (b * r)) ⊤ = ⊤ ∧
    (∀ μ : Ω, Module.End.HasEigenvalue (f.toLinearMap.baseChange Ω) μ →
      μ = ι (b * r) ∧ ν μ = ((1 / 2 - s / 3 : ℚ) : WithTop ℚ)) ∧
    algebraMap L Ω (LinearMap.det f.toLinearMap) =
      ι (b * r) ^ Module.finrank L U ∧
    ν (algebraMap L Ω (LinearMap.det f.toLinearMap)) =
      (((Module.finrank L U : ℚ) * (1 / 2 - s / 3) : ℚ) : WithTop ℚ) ∧
    coefficientNewton ν f = (Module.finrank L U : ℚ) * (1 / 2 - s / 3) := by
  let F : Module.End Ω (Ω ⊗[L] U) := f.toLinearMap.baseChange Ω
  have hnum : F.genEigenspace (ι (b * r)) ⊤ = ⊤ ∧
      ∀ μ, F.HasEigenvalue μ → μ = ι (b * r) ∧
        ν μ = ((1 / 2 - s / 3 : ℚ) : WithTop ℚ) := by
    cases subsingleton_or_nontrivial (Ω ⊗[L] U) with
    | inl hzero =>
      let := hzero
      refine ⟨Subsingleton.elim _ _, ?_⟩
      intro μ hμ
      exact False.elim (hμ (Subsingleton.elim _ _))
    | inr hnonzero =>
      let := hnonzero
      exact forced_frobenius_eigenvalue_and_slope
        q hq jC ι r b e hr hrC hRadialDilation hCentralConstraint_central F T hcomm hΦcomm
        hCubicRelation hCentralConstraint_satake hweight hCommuting ν hνq s hνe
  have hdet : algebraMap L Ω (LinearMap.det f.toLinearMap) =
      ι (b * r) ^ Module.finrank L U := by
    rw [← LinearMap.det_baseChange (A := Ω)]
    have hh := determinant_of_only_eigenvalue F (ι (b * r)) (fun μ hμ => (hnum.2 μ hμ).1)
    simpa only [Module.finrank_baseChange] using hh
  have hval : ν (algebraMap L Ω (LinearMap.det f.toLinearMap)) =
      (((Module.finrank L U : ℚ) * (1 / 2 - s / 3) : ℚ) : WithTop ℚ) := by
    rw [hdet, ν.map_pow,
      valuation_of_forced_root q hq ι r b e hr hCentralConstraint_central ν hνq s hνe]
    simp only [← WithTop.coe_nsmul, nsmul_eq_mul]
  refine ⟨hnum.1, hnum.2, hdet, hval, ?_⟩
  apply WithTop.coe_injective
  simpa [coefficientNewton] using hval

/-- The exact Newton conclusion, retaining every non-comparison graph input
as a named hypothesis. The operator is fixed to the supplied equivalence. -/
def NewtonData
    {K L Ω U : Type*} [Field K] [CharZero K]
    [Field L] [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Algebra L Ω]
    [AddCommGroup U] [Module L U] [FiniteDimensional L U]
    (q : ℕ) (jC : K →+* ℂ) (ι : K →+* Ω) (f : U ≃ₗ[L] U) : Prop :=
  ∀
    (r b e : K) (_hr : r ^ 2 = (q : K))
    (_hrC : jC r = (Real.sqrt (q : ℝ) : ℂ))
    (_hC4_10 : ‖jC e‖ = 1)
    (_hL4_18_central : ∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1)
    (T : Fin 3 → Module.End Ω (Ω ⊗[L] U))
    (_hcomm : ∀ i j, Commute (T i) (T j))
    (_hΦcomm : ∀ i, Commute (f.toLinearMap.baseChange Ω) (T i))
    (_hP4_14 :
      (f.toLinearMap.baseChange Ω) ^ 3 - T 0 * (f.toLinearMap.baseChange Ω) ^ 2 +
        q • (T 1 * (f.toLinearMap.baseChange Ω)) - (q ^ 3) • T 2 = 0)
    (_hL4_18_satake : ∀ i : Fin 3,
      (T i).genEigenspace
        (ι ((![(q : K) * b * (r + r⁻¹ + e),
          (q : K) * b ^ 2 * (r * r⁻¹ + r * e + r⁻¹ * e),
          b ^ 3 * e] : Fin 3 → K) i)) ⊤ = ⊤)
    (_hE67 : CommutingInput Ω (Ω ⊗[L] U))
    (ν : AddValuation Ω (WithTop ℚ)) (_hνq : ν (q : Ω) = 1)
    (s : ℚ) (_hνe : ν (ι e) = (s : WithTop ℚ)),
    Module.End.genEigenspace (f.toLinearMap.baseChange Ω) (ι (b * r)) ⊤ = ⊤ ∧
    (∀ μ : Ω, Module.End.HasEigenvalue (f.toLinearMap.baseChange Ω) μ →
      μ = ι (b * r) ∧ ν μ = ((1 / 2 - s / 3 : ℚ) : WithTop ℚ)) ∧
    algebraMap L Ω (LinearMap.det f.toLinearMap) =
      ι (b * r) ^ Module.finrank L U ∧
    ν (algebraMap L Ω (LinearMap.det f.toLinearMap)) =
      (((Module.finrank L U : ℚ) * (1 / 2 - s / 3) : ℚ) : WithTop ℚ) ∧
    coefficientNewton ν f = (Module.finrank L U : ℚ) * (1 / 2 - s / 3)

lemma newtonData_of_weights
    {K L Ω U : Type*} [Field K] [CharZero K]
    [Field L] [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Algebra L Ω]
    [AddCommGroup U] [Module L U] [FiniteDimensional L U]
    (q : ℕ) (hq : q.Prime) (jC : K →+* ℂ) (ι : K →+* Ω) (f : U ≃ₗ[L] U)
    (hweight : ∀ a : K, Module.End.HasEigenvalue (f.toLinearMap.baseChange Ω) (ι a) →
      ‖jC a‖ = Real.sqrt (q : ℝ)) : NewtonData q jC ι f := by
  intro r b e hr hrC hc hc0 T ht ht0 hp hs h67 ν hν s he
  exact newton_from_weights q hq jC ι f hweight r b e hr hrC hc hc0
    T ht ht0 hp hs h67 ν hν s he

end

noncomputable section

/-! Intrinsic Newton normalization over finite extensions of ℚ_q.
The valuation is computed by the field norm and the ordinary Padic.valuation.
This supplies CMExtraction's normalization after restriction of scalars without an
assumption identifying an abstract Newton function with a determinant. -/

open _root_.Module
open scoped TensorProduct

variable (q : ℕ) [Fact q.Prime]

/-- The normalized local valuation on a finite coefficient field. -/
def localValuation (L : Type*) [Field L] [Algebra ℚ_[q] L]
    [FiniteDimensional ℚ_[q] L] (x : L) : ℚ :=
  (Padic.valuation (Algebra.norm ℚ_[q] x) : ℚ) / Module.finrank ℚ_[q] L

/-- Newton number divided by the coefficient extension degree, exactly the
normalization of the Newton function used in the CMExtraction slope interface. -/
def newton (L U : Type*) [Field L] [Algebra ℚ_[q] L]
    [FiniteDimensional ℚ_[q] L] [AddCommGroup U] [Module L U]
    [Module ℚ_[q] U] [IsScalarTower ℚ_[q] L U]
    [FiniteDimensional L U] (f : U ≃ₗ[L] U) : ℚ :=
  (Padic.valuation (LinearMap.det (f.toLinearMap.restrictScalars ℚ_[q])) : ℚ) /
    Module.finrank ℚ_[q] L

lemma newton_eq_localValuation_det
    (L U : Type*) [Field L] [Algebra ℚ_[q] L]
    [FiniteDimensional ℚ_[q] L] [AddCommGroup U] [Module L U]
    [Module ℚ_[q] U] [IsScalarTower ℚ_[q] L U]
    [FiniteDimensional L U] (f : U ≃ₗ[L] U) :
    newton q L U f = localValuation q L (LinearMap.det f.toLinearMap) := by
  simp only [newton, localValuation, LinearMap.det_restrictScalars]

lemma localValuation_one (L : Type*) [Field L] [Algebra ℚ_[q] L]
    [FiniteDimensional ℚ_[q] L] : localValuation q L 1 = 0 := by
  simp [localValuation]

lemma localValuation_mul (L : Type*) [Field L] [Algebra ℚ_[q] L]
    [FiniteDimensional ℚ_[q] L] (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) :
    localValuation q L (x * y) = localValuation q L x + localValuation q L y := by
  simp only [localValuation, map_mul,
    Padic.valuation_mul (Algebra.norm_ne_zero_iff.mpr hx) (Algebra.norm_ne_zero_iff.mpr hy),
    Int.cast_add, add_div]

lemma localValuation_pow (L : Type*) [Field L] [Algebra ℚ_[q] L]
    [FiniteDimensional ℚ_[q] L] (x : L) (n : ℕ) :
    localValuation q L (x ^ n) = (n : ℚ) * localValuation q L x := by
  simp [localValuation, map_pow, Padic.valuation_pow, mul_div_assoc]

lemma localValuation_q (L : Type*) [Field L] [Algebra ℚ_[q] L]
    [FiniteDimensional ℚ_[q] L] : localValuation q L (q : L) = 1 := by
  have hd : (Module.finrank ℚ_[q] L : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos.ne')
  simp [localValuation, Algebra.norm_natCast, Padic.valuation_pow, hd]

lemma forced_root_localValuation
    (L : Type*) [Field L] [Algebra ℚ_[q] L] [FiniteDimensional ℚ_[q] L]
    (r b e : L) (hr : r ^ 2 = (q : L))
    (hc : ∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1) :
    localValuation q L (b * r) = 1 / 2 - localValuation q L e / 3 := by
  obtain ⟨n, hn, hcn⟩ := hc
  have hbe : b ^ 3 * e ≠ 0 := by
    intro hz
    simp [hz, hn.ne'] at hcn
  have hb : b ≠ 0 := fun hz => hbe (by simp [hz])
  have he : e ≠ 0 := fun hz => hbe (by simp [hz])
  have hr0 : r ≠ 0 := by
    intro hz
    have hqB : (q : ℚ_[q]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
    have hq0 : (q : L) ≠ 0 := by
      simpa only [map_natCast] using (map_ne_zero (algebraMap ℚ_[q] L)).mpr hqB
    exact hq0 (by simpa [hz] using hr.symm)
  have hcval := congrArg (localValuation q L) hcn
  rw [localValuation_pow, localValuation_mul q L _ _ (pow_ne_zero _ hb) he,
    localValuation_pow, localValuation_one] at hcval
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hbval : 3 * localValuation q L b + localValuation q L e = 0 :=
    (mul_eq_zero.mp hcval).resolve_left hnQ
  have hrval := congrArg (localValuation q L) hr
  rw [localValuation_pow, localValuation_q] at hrval
  rw [localValuation_mul q L _ _ hb hr0]
  norm_num at hrval
  linarith

/-- The norm-defined local valuation is independent of enlargement of the
finite coefficient field. This is the precise meaning of ν_ι(e) used below. -/
lemma localValuation_algebraMap
    (L M : Type*) [Field L] [Field M] [Algebra ℚ_[q] L] [Algebra ℚ_[q] M]
    [Algebra L M] [IsScalarTower ℚ_[q] L M]
    [FiniteDimensional ℚ_[q] L] [FiniteDimensional L M] [FiniteDimensional ℚ_[q] M]
    (x : L) : localValuation q M (algebraMap L M x) = localValuation q L x := by
  have hLM : (Module.finrank L M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hQL : (Module.finrank ℚ_[q] L : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hn : Algebra.norm ℚ_[q] (algebraMap L M x) =
      (Algebra.norm ℚ_[q] x) ^ Module.finrank L M := by
    rw [← Algebra.norm_norm (R := ℚ_[q]) (S := L), Algebra.norm_algebraMap, map_pow]
  simp only [localValuation, hn, Padic.valuation_pow, Int.cast_mul, Int.cast_natCast]
  rw [← Module.finrank_mul_finrank ℚ_[q] L M, Nat.cast_mul]
  field_simp

lemma newton_baseChange
    (L M U : Type*) [Field L] [Field M] [Algebra ℚ_[q] L] [Algebra ℚ_[q] M]
    [Algebra L M] [IsScalarTower ℚ_[q] L M]
    [FiniteDimensional ℚ_[q] L] [FiniteDimensional L M] [FiniteDimensional ℚ_[q] M]
    [AddCommGroup U] [Module L U] [Module ℚ_[q] U] [IsScalarTower ℚ_[q] L U]
    [FiniteDimensional L U] (f : U ≃ₗ[L] U) :
    newton q M (M ⊗[L] U) (f.baseChange L M U U) = newton q L U f := by
  rw [newton_eq_localValuation_det, newton_eq_localValuation_det,
    LinearEquiv.coe_baseChange, LinearMap.det_baseChange,
    localValuation_algebraMap]

/-- The intrinsic Newton number of a pure Frobenius, computed from its
actual determinant and the central parameter relation. -/
lemma newton_of_determinant_power
    (L U : Type*) [Field L] [Algebra ℚ_[q] L] [FiniteDimensional ℚ_[q] L]
    [AddCommGroup U] [Module L U] [Module ℚ_[q] U] [IsScalarTower ℚ_[q] L U]
    [FiniteDimensional L U] (f : U ≃ₗ[L] U)
    (r b e : L) (hr : r ^ 2 = (q : L))
    (hc : ∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1)
    (hdet : LinearMap.det f.toLinearMap = (b * r) ^ Module.finrank L U) :
    newton q L U f = (Module.finrank L U : ℚ) *
      (1 / 2 - localValuation q L e / 3) := by
  rw [newton_eq_localValuation_det, hdet, localValuation_pow,
    forced_root_localValuation q L r b e hr hc]

/-- Pass the already derived determinant identity through any finite field
containing the three parameters. The conclusion is CMExtraction's normalized
restriction-of-scalars Newton number on the original summand. -/
lemma intrinsic_newton_after_extension
    {K L M Ω U : Type*} [Field K] [Field L] [Field M] [Field Ω]
    [Algebra ℚ_[q] L] [Algebra ℚ_[q] M] [Algebra L M]
    [IsScalarTower ℚ_[q] L M] [Algebra L Ω] [Algebra M Ω] [IsScalarTower L M Ω]
    [FiniteDimensional ℚ_[q] L] [FiniteDimensional L M] [FiniteDimensional ℚ_[q] M]
    [AddCommGroup U] [Module L U] [Module ℚ_[q] U] [IsScalarTower ℚ_[q] L U]
    [FiniteDimensional L U] (f : U ≃ₗ[L] U) (ι : K →+* Ω)
    (r b e : K) (hr : r ^ 2 = (q : K))
    (hc : ∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1)
    (rM bM eM : M)
    (hrM : algebraMap M Ω rM = ι r)
    (hbM : algebraMap M Ω bM = ι b)
    (heM : algebraMap M Ω eM = ι e)
    (hdet : algebraMap L Ω (LinearMap.det f.toLinearMap) =
      ι (b * r) ^ Module.finrank L U) :
    newton q L U f = (Module.finrank L U : ℚ) *
      (1 / 2 - localValuation q M eM / 3) := by
  have hr' : rM ^ 2 = (q : M) := by
    apply (algebraMap M Ω).injective
    simpa only [map_pow, map_natCast, hrM] using congrArg ι hr
  have hc' : ∃ n : ℕ, 0 < n ∧ (bM ^ 3 * eM) ^ n = 1 := by
    obtain ⟨n, hn, hcn⟩ := hc
    refine ⟨n, hn, (algebraMap M Ω).injective ?_⟩
    simpa only [map_pow, map_mul, map_one, hbM, heM] using congrArg ι hcn
  have hd' : LinearMap.det (f.toLinearMap.baseChange M) =
      (bM * rM) ^ Module.finrank M (M ⊗[L] U) := by
    apply (algebraMap M Ω).injective
    rw [LinearMap.det_baseChange, ← IsScalarTower.algebraMap_apply,
      Module.finrank_baseChange, map_pow, map_mul, hbM, hrM, ← map_mul]
    exact hdet
  have hn := newton_of_determinant_power q M (M ⊗[L] U)
    (f.baseChange L M U U) rM bM eM hr' hc' hd'
  simpa only [newton_baseChange, Module.finrank_baseChange] using hn

/-- Direct bridge from the NewtonData returned on a genuine GeometricComparison summand
to CMExtraction's normalized rational Newton function. The finite extension only
contains the three parameters; it does not carry an assumed Newton identity. -/
theorem intrinsic_newton_from_newtonData
    {K L M Ω U : Type*} [Field K] [CharZero K] [Field L] [Field M]
    [Field Ω] [CharZero Ω] [IsAlgClosed Ω]
    [Algebra ℚ_[q] L] [Algebra ℚ_[q] M] [Algebra L M]
    [IsScalarTower ℚ_[q] L M] [Algebra L Ω] [Algebra M Ω] [IsScalarTower L M Ω]
    [FiniteDimensional ℚ_[q] L] [FiniteDimensional L M] [FiniteDimensional ℚ_[q] M]
    [AddCommGroup U] [Module L U] [Module ℚ_[q] U] [IsScalarTower ℚ_[q] L U]
    [FiniteDimensional L U] (jC : K →+* ℂ) (ι : K →+* Ω) (f : U ≃ₗ[L] U)
    (hdata : NewtonData q jC ι f)
    (r b e : K) (hr : r ^ 2 = (q : K))
    (hrC : jC r = (Real.sqrt (q : ℝ) : ℂ))
    (hRadialDilation : ‖jC e‖ = 1)
    (hCentralConstraint_central : ∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1)
    (T : Fin 3 → Module.End Ω (Ω ⊗[L] U))
    (hcomm : ∀ i j, Commute (T i) (T j))
    (hΦcomm : ∀ i, Commute (f.toLinearMap.baseChange Ω) (T i))
    (hCubicRelation :
      (f.toLinearMap.baseChange Ω) ^ 3 - T 0 * (f.toLinearMap.baseChange Ω) ^ 2 +
        q • (T 1 * (f.toLinearMap.baseChange Ω)) - (q ^ 3) • T 2 = 0)
    (hCentralConstraint_satake : ∀ i : Fin 3,
      (T i).genEigenspace
        (ι ((![(q : K) * b * (r + r⁻¹ + e),
          (q : K) * b ^ 2 * (r * r⁻¹ + r * e + r⁻¹ * e),
          b ^ 3 * e] : Fin 3 → K) i)) ⊤ = ⊤)
    (hCommuting : CommutingInput Ω (Ω ⊗[L] U))
    (ν : AddValuation Ω (WithTop ℚ)) (hνq : ν (q : Ω) = 1)
    (s : ℚ) (hνe : ν (ι e) = (s : WithTop ℚ))
    (rM bM eM : M)
    (hrM : algebraMap M Ω rM = ι r)
    (hbM : algebraMap M Ω bM = ι b)
    (heM : algebraMap M Ω eM = ι e) :
    newton q L U f = (Module.finrank L U : ℚ) *
      (1 / 2 - localValuation q M eM / 3) := by
  have hdet := (hdata r b e hr hrC hRadialDilation hCentralConstraint_central T hcomm hΦcomm
    hCubicRelation hCentralConstraint_satake hCommuting ν hνq s hνe).2.2.1
  exact intrinsic_newton_after_extension q f ι r b e hr hCentralConstraint_central
    rM bM eM hrM hbM heM hdet

/-- Canonical finite enlargement containing all three local parameters. -/
def parameterField
    (L : IntermediateField ℚ_[q] (AlgebraicClosure ℚ_[q]))
    (r b e : AlgebraicClosure ℚ_[q]) : IntermediateField L (AlgebraicClosure ℚ_[q]) :=
  IntermediateField.adjoin L ({r, b, e} : Set (AlgebraicClosure ℚ_[q]))

instance parameterField_finite
    (L : IntermediateField ℚ_[q] (AlgebraicClosure ℚ_[q]))
    (r b e : AlgebraicClosure ℚ_[q]) : FiniteDimensional L (parameterField q L r b e) := by
  let : Algebra.IsAlgebraic L (AlgebraicClosure ℚ_[q]) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ_[q]) (L := L)
  apply IntermediateField.finiteDimensional_adjoin
  intro x _
  exact Algebra.IsIntegral.isIntegral x

instance parameterField_finite_over_base
    (L : IntermediateField ℚ_[q] (AlgebraicClosure ℚ_[q]))
    [FiniteDimensional ℚ_[q] L]
    (r b e : AlgebraicClosure ℚ_[q]) : FiniteDimensional ℚ_[q] (parameterField q L r b e) :=
  Module.Finite.trans (R := ℚ_[q]) L (parameterField q L r b e)

lemma parameters_mem_parameterField
    (L : IntermediateField ℚ_[q] (AlgebraicClosure ℚ_[q]))
    (r b e : AlgebraicClosure ℚ_[q]) :
    r ∈ parameterField q L r b e ∧ b ∈ parameterField q L r b e ∧
      e ∈ parameterField q L r b e := by
  exact ⟨IntermediateField.subset_adjoin L _ (by simp),
    IntermediateField.subset_adjoin L _ (by simp),
    IntermediateField.subset_adjoin L _ (by simp)⟩

/-- The parameter valuation computed in the canonical finite enlargement.
Its value is unchanged by further finite enlargement. -/
def parameterValuation
    (L : IntermediateField ℚ_[q] (AlgebraicClosure ℚ_[q]))
    [FiniteDimensional ℚ_[q] L] (r b e : AlgebraicClosure ℚ_[q]) : ℚ :=
  localValuation q (parameterField q L r b e)
    ⟨e, (parameters_mem_parameterField q L r b e).2.2⟩

/-- Ready-to-use CMExtraction Newton formula for a GeometricComparison coefficient summand.
The coefficient field containing the parameters is constructed, and the
left side is the determinant valuation after actual restriction of scalars. -/
theorem intrinsic_newton_on_coefficient_field
    {K U : Type*} [Field K] [CharZero K]
    (L : IntermediateField ℚ_[q] (AlgebraicClosure ℚ_[q]))
    [FiniteDimensional ℚ_[q] L]
    [AddCommGroup U] [Module L U] [Module ℚ_[q] U] [IsScalarTower ℚ_[q] L U]
    [FiniteDimensional L U]
    (jC : K →+* ℂ) (ι : K →+* AlgebraicClosure ℚ_[q]) (f : U ≃ₗ[L] U)
    (hdata : NewtonData (L := L) (U := U) q jC ι f)
    (r b e : K) (hr : r ^ 2 = (q : K))
    (hrC : jC r = (Real.sqrt (q : ℝ) : ℂ))
    (hRadialDilation : ‖jC e‖ = 1)
    (hCentralConstraint_central : ∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1)
    (T : Fin 3 → Module.End (AlgebraicClosure ℚ_[q]) ((AlgebraicClosure ℚ_[q]) ⊗[L] U))
    (hcomm : ∀ i j, Commute (T i) (T j))
    (hΦcomm : ∀ i, Commute (f.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) (T i))
    (hCubicRelation :
      (f.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) ^ 3 - T 0 * (f.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) ^ 2 +
        q • (T 1 * (f.toLinearMap.baseChange (AlgebraicClosure ℚ_[q]))) - (q ^ 3) • T 2 = 0)
    (hCentralConstraint_satake : ∀ i : Fin 3,
      (T i).genEigenspace
        (ι ((![(q : K) * b * (r + r⁻¹ + e),
          (q : K) * b ^ 2 * (r * r⁻¹ + r * e + r⁻¹ * e),
          b ^ 3 * e] : Fin 3 → K) i)) ⊤ = ⊤)
    (hCommuting : CommutingInput (AlgebraicClosure ℚ_[q]) ((AlgebraicClosure ℚ_[q]) ⊗[L] U))
    (ν : AddValuation (AlgebraicClosure ℚ_[q]) (WithTop ℚ)) (hνq : ν (q : (AlgebraicClosure ℚ_[q])) = 1)
    (s : ℚ) (hνe : ν (ι e) = (s : WithTop ℚ)) :
    newton q L U f = (Module.finrank L U : ℚ) *
      (1 / 2 - parameterValuation q L (ι r) (ι b) (ι e) / 3) := by
  let M := parameterField q L (ι r) (ι b) (ι e)
  let rM : M := ⟨ι r, (parameters_mem_parameterField q L (ι r) (ι b) (ι e)).1⟩
  let bM : M := ⟨ι b, (parameters_mem_parameterField q L (ι r) (ι b) (ι e)).2.1⟩
  let eM : M := ⟨ι e, (parameters_mem_parameterField q L (ι r) (ι b) (ι e)).2.2⟩
  have hdet := (hdata r b e hr hrC hRadialDilation hCentralConstraint_central T hcomm hΦcomm
    hCubicRelation hCentralConstraint_satake hCommuting ν hνq s hνe).2.2.1
  exact intrinsic_newton_after_extension (M := M) q f ι r b e hr hCentralConstraint_central
    rM bM eM rfl rfl rfl hdet

end

end OAI.NumberTheory.PadicHodge.FrobeniusSlopeComparisonNewton
