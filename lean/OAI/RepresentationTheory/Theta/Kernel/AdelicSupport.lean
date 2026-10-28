import OAI.RepresentationTheory.Theta.Kernel.Definitions
import Mathlib.Algebra.Module.ZLattice.Basic

/-! # Adelic Support -/

namespace OAI.RepresentationTheory.Theta.Kernel.AdelicSupport

noncomputable section

section

open scoped BigOperators _root_.Topology
open IsDedekindDomain

open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

lemma local_clear_denominator (v : HeightOneSpectrum ℤ)
    (x : v.adicCompletion ℚ) :
    ∃ n : ℕ, 0 < n ∧ (n : v.adicCompletion ℚ) * x ∈ v.adicCompletionIntegers ℚ := by
  let O := v.adicCompletionIntegers ℚ
  have hopen : IsOpen {y : v.adicCompletion ℚ | x - y ∈ O} :=
    (Valued.isOpen_valuationSubring _).preimage (continuous_const.sub continuous_id)
  have hx : x ∈ {y : v.adicCompletion ℚ | x - y ∈ O} := by simp
  obtain ⟨q, hq⟩ := (v.denseRange_algebraMap ℚ).mem_nhds (hopen.mem_nhds hx)
  refine ⟨q.den, q.den_pos, ?_⟩
  have hm : (q.den : v.adicCompletion ℚ) *
      (x - algebraMap ℚ (v.adicCompletion ℚ) q) ∈ O :=
    O.toSubring.mul_mem (natCast_mem O.toSubring q.den) hq
  have hnum : (q.den : v.adicCompletion ℚ) *
      algebraMap ℚ (v.adicCompletion ℚ) q = (q.num : v.adicCompletion ℚ) := by
    have h := congrArg (algebraMap ℚ (v.adicCompletion ℚ)) q.den_mul_eq_num
    simpa only [map_mul, map_natCast, map_intCast] using h
  have heq : (q.den : v.adicCompletion ℚ) * x =
      (q.den : v.adicCompletion ℚ) *
        (x - algebraMap ℚ (v.adicCompletion ℚ) q) + q.num := by
    rw [mul_sub, hnum]; ring
  rw [heq]
  exact O.toSubring.add_mem hm (intCast_mem O.toSubring q.num)

def integralAdeles : Set Definitions.DerivativeFactorization.AQf :=
  {a | ∀ v : HeightOneSpectrum ℤ, a v ∈ v.adicCompletionIntegers ℚ}

lemma integralAdeles_open : IsOpen integralAdeles := by
  change IsOpen {a : RestrictedProduct
    (fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ)
    (fun v => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) Filter.cofinite |
      ∀ v, a.1 v ∈ v.adicCompletionIntegers ℚ}
  exact RestrictedProduct.isOpen_forall_mem
    (fun v : HeightOneSpectrum ℤ => Valued.isOpen_valuationSubring _)

lemma integralAdeles_nat_mul {a : Definitions.DerivativeFactorization.AQf} (ha : a ∈ integralAdeles) (n : ℕ) :
    (n : Definitions.DerivativeFactorization.AQf) * a ∈ integralAdeles := by
  intro v
  exact (v.adicCompletionIntegers ℚ).toSubring.mul_mem
    (natCast_mem (v.adicCompletionIntegers ℚ).toSubring n) (ha v)

lemma adelic_clear_denominator (a : Definitions.DerivativeFactorization.AQf) :
    ∃ n : ℕ, 0 < n ∧ (n : Definitions.DerivativeFactorization.AQf) * a ∈ integralAdeles := by
  classical
  have hfinite : {v : HeightOneSpectrum ℤ | a v ∉ v.adicCompletionIntegers ℚ}.Finite :=
    a.2
  let S := hfinite.toFinset
  choose n hn hmul using fun v : S => local_clear_denominator v.1 (a v.1)
  refine ⟨∏ v : S, n v, Finset.prod_pos (fun v _ => hn v), ?_⟩
  intro v
  by_cases hv : v ∈ S
  · obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ (⟨v, hv⟩ : S))
    change ((∏ v : S, n v : ℕ) : v.adicCompletion ℚ) * a v ∈ _
    rw [hm, Nat.cast_mul]
    have h := (v.adicCompletionIntegers ℚ).toSubring.mul_mem
      (natCast_mem (v.adicCompletionIntegers ℚ).toSubring m) (hmul ⟨v, hv⟩)
    simpa only [ValuationSubring.mem_toSubring, mul_left_comm, mul_assoc] using h
  · have ha : a v ∈ v.adicCompletionIntegers ℚ := by
      simpa [S] using hv
    exact (v.adicCompletionIntegers ℚ).toSubring.mul_mem
      (natCast_mem (v.adicCompletionIntegers ℚ).toSubring _) ha

variable {ι : Type*} [Fintype ι]

def denominatorSet (n : ℕ) : Set (ι → Definitions.DerivativeFactorization.AQf) :=
  {a | ∀ i, (n : Definitions.DerivativeFactorization.AQf) * a i ∈ integralAdeles}

lemma denominatorSet_open (n : ℕ) : IsOpen (denominatorSet (ι := ι) n) := by
  simp only [denominatorSet, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact integralAdeles_open.preimage (continuous_const.mul (continuous_apply i))

omit [Fintype ι] in
lemma denominatorSet_mono {n m : ℕ} (h : n ∣ m) :
    denominatorSet (ι := ι) n ⊆ denominatorSet m := by
  obtain ⟨k, rfl⟩ := h
  intro a ha i
  simpa only [Nat.cast_mul, mul_left_comm, mul_assoc] using
    integralAdeles_nat_mul (ha i) k

lemma vector_clear_denominator (a : ι → Definitions.DerivativeFactorization.AQf) :
    ∃ n : ℕ, 0 < n ∧ a ∈ denominatorSet n := by
  classical
  choose n hn hmul using fun i => adelic_clear_denominator (a i)
  refine ⟨∏ i, n i, Finset.prod_pos (fun i _ => hn i), ?_⟩
  intro i
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  rw [hm, Nat.cast_mul]
  simpa only [mul_left_comm, mul_assoc] using integralAdeles_nat_mul (hmul i) m

lemma denominator_cover (a : ι → Definitions.DerivativeFactorization.AQf) :
    a ∈ ⋃ n : {n : ℕ // 0 < n}, denominatorSet (ι := ι) n.1 := by
  obtain ⟨n, hn, ha⟩ := vector_clear_denominator a
  exact Set.mem_iUnion.mpr ⟨⟨n, hn⟩, ha⟩

lemma compact_finite_denominators (K : Set (ι → Definitions.DerivativeFactorization.AQf)) (hK : IsCompact K) :
    ∃ S : Finset {n : ℕ // 0 < n},
      K ⊆ ⋃ n ∈ S, denominatorSet (ι := ι) n.1 := by
  exact hK.elim_finite_subcover
    (fun n : {n : ℕ // 0 < n} => denominatorSet (ι := ι) n.1)
    (fun n => denominatorSet_open n.1)
    (fun a _ => denominator_cover a)

lemma compact_clear_denominator (K : Set (ι → Definitions.DerivativeFactorization.AQf)) (hK : IsCompact K) :
    ∃ n : ℕ, 0 < n ∧ K ⊆ denominatorSet n := by
  classical
  obtain ⟨S, hS⟩ := compact_finite_denominators K hK
  refine ⟨∏ n ∈ S, n.1, Finset.prod_pos (fun n _ => n.2), ?_⟩
  intro a ha
  obtain ⟨n, hn, han⟩ := Set.mem_iUnion₂.mp (hS ha)
  have hd : n.1 ∣ ∏ m ∈ S, m.1 := Finset.dvd_prod_of_mem (fun n => n.1) hn
  exact denominatorSet_mono (ι := ι) hd han

lemma input_denominator (φ : Definitions.DerivativeFactorization.Input ι) :
    ∃ n : ℕ, 0 < n ∧ ∀ q : ι → ℚ, φ.1 (Definitions.DerivativeFactorization.diagonal q) ≠ 0 →
      ∀ i, ∃ z : ℤ, (n : ℚ) * q i = z := by
  obtain ⟨n, hn, hbound⟩ := compact_clear_denominator (tsupport φ.1) φ.2.2
  refine ⟨n, hn, ?_⟩
  intro q hq i
  have h := hbound (subset_closure hq) i
  have hint := HeightOneSpectrum.mem_integers_of_valuation_le_one
    (R := ℤ) ℚ ((n : ℚ) * q i) (fun v => ?_)
  · obtain ⟨z, hz⟩ := hint
    exact ⟨z, hz.symm⟩
  · have heq : (n : Definitions.DerivativeFactorization.AQf) * Definitions.DerivativeFactorization.diagonal q i =
        algebraMap ℚ Definitions.DerivativeFactorization.AQf ((n : ℚ) * q i) := by simp [Definitions.DerivativeFactorization.diagonal]
    have hv := h v
    rw [heq, FiniteAdeleRing.algebraMap_apply] at hv
    simpa only [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using hv

end

open scoped BigOperators

open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization
variable {ι : Type*} [Fintype ι]

lemma coordinate_lattice_mem (x : ι → ℝ) :
    x ∈ AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι ↔ ∃ z : ι → ℤ, ∀ i, x i = z i := by
  classical
  rw [AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    intro i
    have hi := congrFun hz i
    simpa [Pi.basisFun_apply, Pi.single_apply, mul_ite] using hi.symm
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    ext i
    simpa [Pi.basisFun_apply, Pi.single_apply, mul_ite] using (hz i).symm

lemma input_lattice_presentation (φ : Definitions.DerivativeFactorization.Input ι) :
    ∃ (L : Submodule ℤ (ι → ℝ)) (_ : DiscreteTopology L)
      (q : L → (ι → ℚ)),
      Function.Injective q ∧
      (∀ x : L, Definitions.DerivativeFactorization.realPosition (q x) = (x : ι → ℝ)) ∧
      (∀ r : ι → ℚ, φ.1 (Definitions.DerivativeFactorization.diagonal r) ≠ 0 → r ∈ Set.range q) := by
  classical
  obtain ⟨n, hn, hden⟩ := input_denominator φ
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  let e : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := (n : ℝ) • LinearMap.id
  let L := ZLattice.comap ℝ (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) e
  have hec : Continuous e := continuous_const.smul continuous_id
  have hei : Function.Injective e := by
    intro x y h
    exact (smul_right_injective _ hnR) h
  let : DiscreteTopology L :=
    ZLattice.comap_discreteTopology ℝ (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) hec hei
  have hrational : ∀ x : L, ∃ r : ι → ℚ, Definitions.DerivativeFactorization.realPosition r = (x : ι → ℝ) := by
    intro x
    obtain ⟨z, hz⟩ := (coordinate_lattice_mem (e x)).mp x.2
    refine ⟨fun i => (z i : ℚ) / n, ?_⟩
    ext i
    change (((z i : ℚ) / n : ℚ) : ℝ) = (x : ι → ℝ) i
    push_cast
    apply (div_eq_iff hnR).mpr
    simpa [e, mul_comm] using (hz i).symm
  choose q hq using hrational
  refine ⟨L, inferInstance, q, ?_, hq, ?_⟩
  · intro x y h
    apply Subtype.ext
    rw [← hq x, ← hq y, h]
  · intro r hr
    have hmem : Definitions.DerivativeFactorization.realPosition r ∈ L := by
      apply (coordinate_lattice_mem (e (Definitions.DerivativeFactorization.realPosition r))).mpr
      choose z hz using hden r hr
      refine ⟨z, ?_⟩
      intro i
      have hi := congrArg (fun a : ℚ => (a : ℝ)) (hz i)
      simpa [e, Definitions.DerivativeFactorization.realPosition] using hi
    refine ⟨⟨Definitions.DerivativeFactorization.realPosition r, hmem⟩, ?_⟩
    funext i
    have hi := congrFun (hq ⟨Definitions.DerivativeFactorization.realPosition r, hmem⟩) i
    exact Rat.cast_injective hi

omit [Fintype ι] in
lemma input_bounded (φ : Definitions.DerivativeFactorization.Input ι) : ∃ C : ℝ, ∀ x, ‖φ.1 x‖ ≤ C := by
  have h := φ.2.2.isCompact_range φ.2.1.continuous
  obtain ⟨C, hC⟩ := h.exists_bound_of_continuousOn (f := id) continuous_id.continuousOn
  exact ⟨C, fun x => hC (φ.1 x) (Set.mem_range_self x)⟩

end

end OAI.RepresentationTheory.Theta.Kernel.AdelicSupport
