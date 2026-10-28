import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GenericPolynomialGCD

/-! # Generic Holomorphic Polynomial -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GenericHolomorphicPolynomial.Constructions.GenericPolynomial

noncomputable section

/-!
# A generic common-root polynomial for a holomorphic family

Denominator-cleared identities over the local ring are realized on a common
neighborhood. Outside one holomorphic exceptional zero set, a finite family
of polynomial equations has exactly the roots of one polynomial family.
-/

open Set Filter _root_.Polynomial
open scoped _root_.Topology BigOperators

private theorem exists_representative {X R : Type*} {l : Filter X} (a : Germ l R) :
    ∃ f : X → R, a = (f : Germ l R) :=
  a.inductionOn (fun f => ⟨f, rfl⟩)

theorem exists_generic_common_root_family
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype ι]
    (P : ι → E → ℂ[X]) {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) (d : ℕ)
    (hcoeff : ∀ i k, DifferentiableOn ℂ (fun y => (P i y).coeff k) U)
    (hdegree : ∀ i y, y ∈ U → (P i y).natDegree ≤ d)
    (hnonzero : ∃ i, P i x ≠ 0) :
    ∃ (D : ℕ) (G : E → ℂ[X]) (c : E → ℂ) (V : Set E),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      (∀ y, (G y).natDegree ≤ D) ∧
      (∀ k, DifferentiableOn ℂ (fun y => (G y).coeff k) V) ∧
      DifferentiableOn ℂ c V ∧ (¬∀ᶠ y in 𝓝 x, c y = 0) ∧
      ∀ y ∈ V, c y ≠ 0 → ∀ z : ℂ, (∀ i, (P i y).eval z = 0) ↔ (G y).eval z = 0 := by
  classical
  let p : ι → (HolomorphicGerms.Constructions.Germs.HolomorphicGerm x)[X] := fun i =>
    PolynomialGerms.Constructions.Germs.polynomialOfFamily x (P i) d hU hx (hcoeff i)
  have hp (i : ι) : PolynomialGerms.Constructions.Germs.polynomialRealization x (p i) = ((P i) : Germ (𝓝 x) ℂ[X]) :=
    PolynomialGerms.Constructions.Germs.realize_polynomialOfFamily x (P i) d hU hx (hcoeff i) (hdegree i)
  have hpn : ∃ i, p i ≠ 0 := by
    obtain ⟨i, hi⟩ := hnonzero
    exact ⟨i, PolynomialGerms.Constructions.Germs.polynomialOfFamily_ne_zero x (P i) d hU hx (hcoeff i) (hdegree i) hi⟩
  obtain ⟨q, a₀, B, a, H, _, ha₀, ha, hB, hH⟩ := GenericPolynomialGCD.Constructions.GenericGCD.exists_generic_certificate p hpn
  obtain ⟨D, G, W, hW, hxW, hGdeg, hGcoeff, hq⟩ := PolynomialGerms.Constructions.Germs.exists_polynomial_representative x q
  choose b hb using (fun i => exists_representative (PolynomialGerms.Constructions.Germs.polynomialRealization x (B i)))
  choose h hh using (fun i => exists_representative (PolynomialGerms.Constructions.Germs.polynomialRealization x (H i)))
  obtain ⟨f₀, hf₀, _⟩ := a₀.property
  have harep : ∀ i, ∃ f : E → ℂ, (f : Germ (𝓝 x) ℂ) = (a i).val := by
    intro i
    obtain ⟨f, hf, _⟩ := (a i).property
    exact ⟨f, hf⟩
  choose f hf using harep
  let ac : HolomorphicGerms.Constructions.Germs.HolomorphicGerm x := a₀ * ∏ i, a i
  have hac : ac ≠ 0 := mul_ne_zero ha₀ (Finset.prod_ne_zero_iff.mpr (fun i _ => ha i))
  obtain ⟨c, hc, Wc, hWc, hxWc, hcd⟩ := ac.property
  have hc0 : ¬∀ᶠ y in 𝓝 x, c y = 0 := by
    intro hc0
    apply hac
    apply Subtype.ext
    change ac.val = 0
    rw [← hc]
    exact Germ.coe_eq.mpr hc0
  have hfactor : ∀ᶠ y in 𝓝 x, c y = f₀ y * ∏ i, f i y := by
    have heq : (c : Germ (𝓝 x) ℂ) = ((f₀ * ∏ i, f i : E → ℂ) : Germ (𝓝 x) ℂ) := by
      rw [hc, Germ.coe_mul, Germ.coe_prod, hf₀]
      change (HolomorphicGerms.Constructions.Germs.holomorphicGerms x).subtype (a₀ * ∏ i, a i) = _
      rw [map_mul, map_prod]
      simp only [hf]
      rfl
    filter_upwards [Germ.coe_eq.mp heq] with y hy
    simpa only [Pi.mul_apply, Finset.prod_apply] using hy
  have hsum : ∀ᶠ y in 𝓝 x, (∑ i, b i y * P i y) = C (f₀ y) * G y := by
    have heq := congrArg (PolynomialGerms.Constructions.Germs.polynomialRealization x) hB
    simp only [map_sum, map_mul, hb, hp,
      PolynomialGerms.Constructions.Germs.realize_C_of_representative x a₀ f₀ hf₀, hq, ← Germ.coe_mul, ← Germ.coe_sum] at heq
    filter_upwards [Germ.coe_eq.mp heq] with y hy
    simpa only [Pi.mul_apply, Finset.sum_apply] using hy
  have hdiv : ∀ i, ∀ᶠ y in 𝓝 x, C (f i y) * P i y = G y * h i y := by
    intro i
    have heq := congrArg (PolynomialGerms.Constructions.Germs.polynomialRealization x) (hH i)
    simp only [map_mul, PolynomialGerms.Constructions.Germs.realize_C_of_representative x (a i) (f i) (hf i),
      hp, hq, hh, ← Germ.coe_mul] at heq
    exact Germ.coe_eq.mp heq
  have hall : ∀ᶠ y in 𝓝 x, y ∈ U ∧ y ∈ W ∧ y ∈ Wc ∧
      c y = f₀ y * ∏ i, f i y ∧ (∑ i, b i y * P i y) = C (f₀ y) * G y ∧
      ∀ i, C (f i y) * P i y = G y * h i y := by
    filter_upwards [hU.mem_nhds hx, hW.mem_nhds hxW, hWc.mem_nhds hxWc,
      hfactor, hsum, eventually_all.mpr hdiv] with y hyU hyW hyWc hyf hys hyd
    exact ⟨hyU, hyW, hyWc, hyf, hys, hyd⟩
  obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp hall
  refine ⟨D, G, c, V, hV, hxV, fun y hy => (hVsub hy).1, hGdeg,
    fun k => (hGcoeff k).mono (fun y hy => (hVsub hy).2.1),
    hcd.mono (fun y hy => (hVsub hy).2.2.1), hc0, ?_⟩
  intro y hy hcy z
  obtain ⟨_, _, _, hfy, hBy, hHy⟩ := hVsub hy
  have hnon : f₀ y * ∏ i, f i y ≠ 0 := hfy ▸ hcy
  have hf₀y : f₀ y ≠ 0 := (mul_ne_zero_iff.mp hnon).1
  have hfiy (i : ι) : f i y ≠ 0 := Finset.prod_ne_zero_iff.mp
    (mul_ne_zero_iff.mp hnon).2 i (Finset.mem_univ _)
  constructor
  · intro hz
    have heq := congrArg (fun Q : ℂ[X] => Q.eval z) hBy
    have hmul : f₀ y * (G y).eval z = 0 := by
      simpa only [eval_finsetSum, eval_mul, eval_C, hz, mul_zero, Finset.sum_const_zero] using heq.symm
    exact (mul_eq_zero.mp hmul).resolve_left hf₀y
  · intro hz i
    have heq := congrArg (fun Q : ℂ[X] => Q.eval z) (hHy i)
    have hmul : f i y * (P i y).eval z = 0 := by
      simpa only [eval_mul, eval_C, hz, zero_mul] using heq
    exact (mul_eq_zero.mp hmul).resolve_left (hfiy i)

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GenericHolomorphicPolynomial.Constructions.GenericPolynomial
