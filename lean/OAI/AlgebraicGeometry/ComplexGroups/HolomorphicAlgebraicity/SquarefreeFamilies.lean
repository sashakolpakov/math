import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GenericSquarefree
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GenericDegree

/-! # Squarefree Families -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SquarefreeFamilies

noncomputable section

/-!
# Squarefree holomorphic polynomial families

Realize the denominator-cleared radical and Bezout identities on a common
neighborhood. Their nonzero scalar factors define the exceptional set.
-/

open Set Filter _root_.Polynomial
open scoped _root_.Topology

namespace Constructions.Germs

def derivativeGerm {X : Type*} (l : Filter X) : Germ l ℂ[X] →+ Germ l ℂ[X] where
  toFun := Germ.map Polynomial.derivative
  map_zero' := by
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun _ => derivative_zero)
  map_add' := by
    intro a b
    induction a, b using Germ.inductionOn₂ with
    | h f g =>
      apply Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall (fun _ => derivative_add)

theorem realize_monomial_of_representative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (x : E) (a : HolomorphicGerms.Constructions.Germs.HolomorphicGerm x) (f : E → ℂ) (hf : (f : Germ (𝓝 x) ℂ) = a.val)
    (n : ℕ) : PolynomialGerms.Constructions.Germs.polynomialRealization x (monomial n a) =
      ((fun y => monomial n (f y)) : Germ (𝓝 x) ℂ[X]) := by
  rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow,
    PolynomialGerms.Constructions.Germs.realize_C_of_representative x a f hf]
  have hX : PolynomialGerms.Constructions.Germs.polynomialRealization x X = ((fun _ : E => (X : ℂ[X])) : Germ (𝓝 x) ℂ[X]) := by
    exact eval₂_X _ _
  rw [hX, ← Germ.coe_pow, ← Germ.coe_mul]
  apply Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall (fun _ => C_mul_X_pow_eq_monomial)

theorem realize_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (x : E) (P : (HolomorphicGerms.Constructions.Germs.HolomorphicGerm x)[X]) :
    PolynomialGerms.Constructions.Germs.polynomialRealization x (derivative P) = derivativeGerm (𝓝 x) (PolynomialGerms.Constructions.Germs.polynomialRealization x P) := by
  induction P using Polynomial.induction_on' with
  | add P Q ihP ihQ => simp only [map_add, ihP, ihQ]
  | monomial n a =>
    obtain ⟨f, hf, _⟩ := a.property
    rw [derivative_monomial, ← monomial_mul_C, map_mul,
      realize_monomial_of_representative x a f hf,
      realize_monomial_of_representative x a f hf]
    have hn : PolynomialGerms.Constructions.Germs.polynomialRealization x (C (n : HolomorphicGerms.Constructions.Germs.HolomorphicGerm x)) =
        ((fun _ : E => C (n : ℂ)) : Germ (𝓝 x) ℂ[X]) := by
      rw [map_natCast, map_natCast]
      rfl
    rw [hn, ← Germ.coe_mul]
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun y => by
      simp only [Pi.mul_apply, monomial_mul_C, Function.comp_apply, derivative_monomial])

end Constructions.Germs

namespace Constructions.GenericPolynomial

private theorem exists_representative {X R : Type*} {l : Filter X} (a : Germ l R) :
    ∃ f : X → R, a = (f : Germ l R) :=
  a.inductionOn (fun f => ⟨f, rfl⟩)

theorem exists_squarefree_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : E → ℂ[X]) {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) (d : ℕ)
    (hcoeff : ∀ k, DifferentiableOn ℂ (fun y => (P y).coeff k) U)
    (hdegree : ∀ y ∈ U, (P y).natDegree ≤ d)
    (hn : ¬∀ᶠ y in 𝓝 x, P y = 0) :
    ∃ (D : ℕ) (Q : E → ℂ[X]) (c : E → ℂ) (V : Set E),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ (∀ y, (Q y).natDegree ≤ D) ∧
      (∀ k, DifferentiableOn ℂ (fun y => (Q y).coeff k) V) ∧
      DifferentiableOn ℂ c V ∧ (¬∀ᶠ y in 𝓝 x, c y = 0) ∧
      ∀ y ∈ V, c y ≠ 0 → (Q y).Separable ∧
        ∀ z : ℂ, (P y).eval z = 0 ↔ (Q y).eval z = 0 := by
  let p := PolynomialGerms.Constructions.Germs.polynomialOfFamily x P d hU hx hcoeff
  have hp : PolynomialGerms.Constructions.Germs.polynomialRealization x p = (P : Germ (𝓝 x) ℂ[X]) :=
    PolynomialGerms.Constructions.Germs.realize_polynomialOfFamily x P d hU hx hcoeff hdegree
  have hpn : p ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hp
    exact hn (Germ.coe_eq.mp hp.symm)
  obtain ⟨q, n, a, b, c₀, H, J, B, C₀, _, ha, hb, hc₀, hH, hJ, hBC⟩ :=
    GenericSquarefree.Constructions.GenericGCD.exists_squarefree_certificate p hpn
  obtain ⟨D, Q, W, hW, hxW, hQdegree, hQcoeff, hq⟩ := PolynomialGerms.Constructions.Germs.exists_polynomial_representative x q
  obtain ⟨f, hf, _⟩ := a.property
  obtain ⟨g, hg, _⟩ := b.property
  obtain ⟨h, hh, _⟩ := c₀.property
  obtain ⟨H', hH'⟩ := exists_representative (PolynomialGerms.Constructions.Germs.polynomialRealization x H)
  obtain ⟨J', hJ'⟩ := exists_representative (PolynomialGerms.Constructions.Germs.polynomialRealization x J)
  obtain ⟨B', hB'⟩ := exists_representative (PolynomialGerms.Constructions.Germs.polynomialRealization x B)
  obtain ⟨C', hC'⟩ := exists_representative (PolynomialGerms.Constructions.Germs.polynomialRealization x C₀)
  let ac := a * b * c₀
  have hac : ac ≠ 0 := mul_ne_zero (mul_ne_zero ha hb) hc₀
  obtain ⟨c, hc, Wc, hWc, hxWc, hcd⟩ := ac.property
  have hcn : ¬∀ᶠ y in 𝓝 x, c y = 0 := by
    intro hz
    apply hac
    apply Subtype.ext
    change ac.val = 0
    rw [← hc]
    exact Germ.coe_eq.mpr hz
  have hfactor : ∀ᶠ y in 𝓝 x, c y = f y * g y * h y := by
    have heq : (c : Germ (𝓝 x) ℂ) = ((fun y => f y * g y * h y) : Germ (𝓝 x) ℂ) := by
      rw [hc]
      change ac.val = ((f * g * h : E → ℂ) : Germ (𝓝 x) ℂ)
      rw [Germ.coe_mul, Germ.coe_mul, hf, hg, hh]
      rfl
    exact Germ.coe_eq.mp heq
  have hdiv : ∀ᶠ y in 𝓝 x, C (f y) * P y = Q y * H' y := by
    have heq := congrArg (PolynomialGerms.Constructions.Germs.polynomialRealization x) hH
    simp only [map_mul, PolynomialGerms.Constructions.Germs.realize_C_of_representative x a f hf,
      hp, hq, hH', ← Germ.coe_mul] at heq
    exact Germ.coe_eq.mp heq
  have hpow : ∀ᶠ y in 𝓝 x, C (g y) * Q y ^ (n + 1) = P y * J' y := by
    have heq := congrArg (PolynomialGerms.Constructions.Germs.polynomialRealization x) hJ
    simp only [map_mul, map_pow, PolynomialGerms.Constructions.Germs.realize_C_of_representative x b g hg,
      hp, hq, hJ', ← Germ.coe_pow, ← Germ.coe_mul] at heq
    exact Germ.coe_eq.mp heq
  have hbezout : ∀ᶠ y in 𝓝 x, B' y * Q y + C' y * derivative (Q y) = C (h y) := by
    have heq := congrArg (PolynomialGerms.Constructions.Germs.polynomialRealization x) hBC
    simp only [map_add, map_mul, PolynomialGerms.Constructions.Germs.realize_C_of_representative x c₀ h hh,
      Germs.realize_derivative, hq, hB', hC'] at heq
    change (B' : Germ (𝓝 x) ℂ[X]) * Q + C' *
      ((fun y => derivative (Q y)) : Germ (𝓝 x) ℂ[X]) =
      ((fun y => C (h y)) : Germ (𝓝 x) ℂ[X]) at heq
    rw [← Germ.coe_mul, ← Germ.coe_mul, ← Germ.coe_add] at heq
    exact Germ.coe_eq.mp heq
  have hall : ∀ᶠ y in 𝓝 x, y ∈ U ∧ y ∈ W ∧ y ∈ Wc ∧
      c y = f y * g y * h y ∧ C (f y) * P y = Q y * H' y ∧
      C (g y) * Q y ^ (n + 1) = P y * J' y ∧
      B' y * Q y + C' y * derivative (Q y) = C (h y) := by
    filter_upwards [hU.mem_nhds hx, hW.mem_nhds hxW, hWc.mem_nhds hxWc,
      hfactor, hdiv, hpow, hbezout] with y hyU hyW hyWc hyf hyd hyp hyb
    exact ⟨hyU, hyW, hyWc, hyf, hyd, hyp, hyb⟩
  obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp hall
  refine ⟨D, Q, c, V, hV, hxV, fun y hy => (hVsub hy).1, hQdegree,
    fun k => (hQcoeff k).mono (fun y hy => (hVsub hy).2.1),
    hcd.mono (fun y hy => (hVsub hy).2.2.1), hcn, ?_⟩
  intro y hy hcy
  obtain ⟨_, _, _, hyf, hyd, hyp, hyb⟩ := hVsub hy
  have hnon : f y * g y * h y ≠ 0 := hyf ▸ hcy
  have hfy : f y ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hnon).1).1
  have hgy : g y ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hnon).1).2
  have hhy : h y ≠ 0 := (mul_ne_zero_iff.mp hnon).2
  constructor
  · apply (separable_def' _).mpr
    refine ⟨C (h y)⁻¹ * B' y, C (h y)⁻¹ * C' y, ?_⟩
    calc
      _ = C (h y)⁻¹ * (B' y * Q y + C' y * derivative (Q y)) := by ring
      _ = 1 := by rw [hyb, ← C_mul, inv_mul_cancel₀ hhy, C_1]
  · intro z
    constructor
    · intro hz
      have heq := congrArg (fun R : ℂ[X] => R.eval z) hyp
      have hpz : g y * (Q y).eval z ^ (n + 1) = 0 := by
        simpa only [eval_mul, eval_C, eval_pow, hz, zero_mul] using heq
      exact (pow_eq_zero_iff (Nat.succ_ne_zero n)).mp ((mul_eq_zero.mp hpz).resolve_left hgy)
    · intro hz
      have heq := congrArg (fun R : ℂ[X] => R.eval z) hyd
      have hpz : f y * (P y).eval z = 0 := by
        simpa only [eval_mul, eval_C, hz, zero_mul] using heq
      exact (mul_eq_zero.mp hpz).resolve_left hfy

theorem exists_monic_separable_common_root_family
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype ι]
    (P : ι → E → ℂ[X]) {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) (d : ℕ)
    (hcoeff : ∀ i k, DifferentiableOn ℂ (fun y => (P i y).coeff k) U)
    (hdegree : ∀ i y, y ∈ U → (P i y).natDegree ≤ d)
    (hnever : ∀ y ∈ U, ∃ i, P i y ≠ 0) :
    ∃ (k : ℕ) (Q : E → ℂ[X]) (c : E → ℂ) (V : Set E),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ DifferentiableOn ℂ c V ∧
      (¬∀ᶠ y in 𝓝 x, c y = 0) ∧
      (∀ j, DifferentiableOn ℂ (fun y => (Q y).coeff j) {y | y ∈ V ∧ c y ≠ 0}) ∧
      ∀ y ∈ V, c y ≠ 0 → (Q y).Monic ∧ (Q y).natDegree = k ∧ (Q y).Separable ∧
        ∀ z : ℂ, (∀ i, (P i y).eval z = 0) ↔ (Q y).eval z = 0 := by
  obtain ⟨D, G, c₁, W₁, hW₁, hxW₁, hW₁U, hGdeg, hGcoeff, hc₁, hc₁n, hGroot⟩ :=
    GenericHolomorphicPolynomial.Constructions.GenericPolynomial.exists_generic_common_root_family P hU hx d hcoeff hdegree (hnever x hx)
  have hGn : ¬∀ᶠ y in 𝓝 x, G y = 0 := by
    intro hz
    apply hc₁n
    filter_upwards [hz, hW₁.mem_nhds hxW₁] with y hy hyW
    by_contra hcy
    obtain ⟨i, hi⟩ := hnever y (hW₁U hyW)
    apply hi
    apply Polynomial.zero_of_eval_zero
    intro z
    exact ((hGroot y hyW hcy z).mpr (by simp only [hy, eval_zero])) i
  obtain ⟨D₂, G₂, c₂, W₂, hW₂, hxW₂, hW₂W₁, hG₂deg, hG₂coeff, hc₂, hc₂n, hG₂⟩ :=
    exists_squarefree_family G hW₁ hxW₁ D hGcoeff (fun y _ => hGdeg y) hGn
  have hG₂n : ¬∀ᶠ y in 𝓝 x, G₂ y = 0 := by
    intro hz
    apply hc₂n
    filter_upwards [hz, hW₂.mem_nhds hxW₂] with y hy hyW
    by_contra hcy
    exact (hG₂ y hyW hcy).1.ne_zero hy
  obtain ⟨k, _, hkn, hkdeg⟩ := GenericDegree.Constructions.GenericPolynomial.exists_generic_degree hG₂deg hG₂n
  obtain ⟨Z, hZsub, hZ, hxZ⟩ := mem_nhds_iff.mp hkdeg
  let c : E → ℂ := fun y => c₁ y * c₂ y * (G₂ y).coeff k
  let Q : E → ℂ[X] := fun y => ((G₂ y).coeff k)⁻¹ • G₂ y
  have hc₁W₂ := hc₁.mono hW₂W₁
  have hcn : ¬∀ᶠ y in 𝓝 x, c y = 0 :=
    GenericDegree.Constructions.GenericPolynomial.not_eventually_zero_mul hW₂ hxW₂ (hc₁W₂.fun_mul hc₂) (hG₂coeff k)
      (GenericDegree.Constructions.GenericPolynomial.not_eventually_zero_mul hW₂ hxW₂ hc₁W₂ hc₂ hc₁n hc₂n) hkn
  have hparts (y : E) (hy : c y ≠ 0) :
      c₁ y ≠ 0 ∧ c₂ y ≠ 0 ∧ (G₂ y).coeff k ≠ 0 :=
    ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hy).1).1,
      (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hy).1).2, (mul_ne_zero_iff.mp hy).2⟩
  refine ⟨k, Q, c, W₂ ∩ Z, hW₂.inter hZ, ⟨hxW₂, hxZ⟩,
    fun y hy => hW₁U (hW₂W₁ hy.1),
    ((hc₁W₂.fun_mul hc₂).fun_mul (hG₂coeff k)).mono inter_subset_left, hcn, ?_, ?_⟩
  · intro j
    have hsub : {y | y ∈ W₂ ∩ Z ∧ c y ≠ 0} ⊆ W₂ := fun _ hy => hy.1.1
    simp only [Q, coeff_smul, smul_eq_mul]
    exact ((hG₂coeff k).mono hsub).fun_inv (fun y hy => (hparts y hy.2).2.2) |>.fun_mul
      ((hG₂coeff j).mono hsub)
  · intro y hy hcy
    obtain ⟨hc₁y, hc₂y, hlead⟩ := hparts y hcy
    have hQdeg : (Q y).natDegree ≤ k := (natDegree_smul_le _ _).trans (hZsub hy.2)
    have hQcoeff : (Q y).coeff k = 1 := by
      simp only [Q, coeff_smul, smul_eq_mul, inv_mul_cancel₀ hlead]
    refine ⟨monic_of_natDegree_le_of_coeff_eq_one k hQdeg hQcoeff,
      le_antisymm hQdeg (le_natDegree_of_ne_zero (by rw [hQcoeff]; exact one_ne_zero)), ?_, ?_⟩
    · change (((G₂ y).coeff k)⁻¹ • G₂ y).Separable
      rw [← C_mul']
      exact Separable.unit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hlead)))
        (hG₂ y hy.1 hc₂y).1
    · intro z
      change (∀ i, (P i y).eval z = 0) ↔ (((G₂ y).coeff k)⁻¹ • G₂ y).eval z = 0
      rw [eval_smul, smul_eq_mul, mul_eq_zero, or_iff_right (inv_ne_zero hlead)]
      exact (hGroot y (hW₂W₁ hy.1) hc₁y z).trans ((hG₂ y hy.1 hc₂y).2 z)

end Constructions.GenericPolynomial

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SquarefreeFamilies
