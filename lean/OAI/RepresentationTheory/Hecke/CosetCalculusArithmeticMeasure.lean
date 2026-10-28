import OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear

/-! # Coset Calculus Arithmetic Measure -/

namespace OAI.RepresentationTheory.Hecke.CosetCalculusArithmeticMeasure

noncomputable section

section

/-! Elementary valuation and matrix calculations for CosetCalculus. -/

open scoped BigOperators

variable {R F : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F]

abbrev Mat (A : Type*) := Matrix (Fin 3) (Fin 3) A

def IntegralElement (x : F) : Prop := x ∈ (algebraMap R F).range

def IntegralMatrix (A : Mat F) : Prop :=
  A ∈ ((algebraMap R F).mapMatrix : Mat R →+* Mat F).range

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] in
lemma integralMatrix_iff (A : Mat F) :
    IntegralMatrix (R := R) A ↔ ∀ i j, IntegralElement (R := R) (A i j) := by
  classical
  constructor
  · rintro ⟨B, rfl⟩ i j
    exact ⟨B i j, rfl⟩
  · intro h
    choose B hB using h
    exact ⟨B, Matrix.ext fun i j => hB i j⟩

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma integral_zpow (π : R) (hπ : Irreducible π) (a : ℤ) :
    IntegralElement (R := R) ((algebraMap R F π) ^ a) ↔ 0 ≤ a :=
  OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.integral_zpow_iff hπ a

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma zpow_eq_unit_mul_iff (π : R) (hπ : Irreducible π) (a b : ℤ) :
    (∃ u : Rˣ, (algebraMap R F π) ^ a =
      algebraMap R F (u : R) * (algebraMap R F π) ^ b) ↔ a = b := by
  have hp := OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.uniformizer_map_ne_zero (K := F) hπ
  constructor
  · rintro ⟨u, hu⟩
    have h : (algebraMap R F π) ^ (a - b) = algebraMap R F (u : R) := by
      rw [zpow_sub₀ hp, hu, mul_div_cancel_right₀ _ (zpow_ne_zero _ hp)]
    have hz := OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.exponent_zero_of_unit π hπ (a - b) u h
    omega
  · rintro rfl
    exact ⟨1, by simp⟩

def triangular (p : F) (a : Fin 3 → ℤ) (x y z : F) : Mat F :=
  !![p ^ a 0, p ^ a 0 * x, p ^ a 0 * y;
     0, p ^ a 1, p ^ a 1 * z;
     0, 0, p ^ a 2]

lemma triangular_det (p : F) (hp : p ≠ 0) (a : Fin 3 → ℤ) (x y z : F) :
    (triangular p a x y z).det = p ^ (a 0 + a 1 + a 2) := by
  simp [triangular, Matrix.det_fin_three, zpow_add₀ hp, mul_assoc]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] in
lemma triangular_integral (π : R) (a : Fin 3 → ℤ) (x y z : F) :
    IntegralMatrix (R := R) (triangular (algebraMap R F π) a x y z) ↔
      IntegralElement (R := R) ((algebraMap R F π) ^ a 0) ∧
      IntegralElement (R := R) ((algebraMap R F π) ^ a 1) ∧
      IntegralElement (R := R) ((algebraMap R F π) ^ a 2) ∧
      IntegralElement (R := R) ((algebraMap R F π) ^ a 0 * x) ∧
      IntegralElement (R := R) ((algebraMap R F π) ^ a 0 * y) ∧
      IntegralElement (R := R) ((algebraMap R F π) ^ a 1 * z) := by
  rw [integralMatrix_iff]
  constructor
  · intro h
    exact ⟨h 0 0, h 1 1, h 2 2, h 0 1, h 0 2, h 1 2⟩
  · rintro ⟨h00, h11, h22, h01, h02, h12⟩ i j
    fin_cases i <;> fin_cases j
    all_goals first
      | exact h00
      | exact h11
      | exact h22
      | exact h01
      | exact h02
      | exact h12
      | exact ⟨0, map_zero (algebraMap R F)⟩

lemma nonnegative_triple_sum_one (a : Fin 3 → ℤ)
    (ha : ∀ i, 0 ≤ a i) (hs : a 0 + a 1 + a 2 = 1) :
    a = ![1, 0, 0] ∨ a = ![0, 1, 0] ∨ a = ![0, 0, 1] := by
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have hc : (a 0 = 1 ∧ a 1 = 0 ∧ a 2 = 0) ∨
      (a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 0) ∨
      (a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 1) := by omega
  rcases hc with h | h | h
  · left; ext i; fin_cases i <;> simp [h]
  · right; left; ext i; fin_cases i <;> simp [h]
  · right; right; ext i; fin_cases i <;> simp [h]

lemma bounded_triple_sum_two (a : Fin 3 → ℤ)
    (ha : ∀ i, a i ≤ 1) (hs : a 0 + a 1 + a 2 = 2) :
    a = ![1, 1, 0] ∨ a = ![1, 0, 1] ∨ a = ![0, 1, 1] := by
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have hc : (a 0 = 1 ∧ a 1 = 1 ∧ a 2 = 0) ∨
      (a 0 = 1 ∧ a 1 = 0 ∧ a 2 = 1) ∨
      (a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 1) := by omega
  rcases hc with h | h | h
  · left; ext i; fin_cases i <;> simp [h]
  · right; left; ext i; fin_cases i <;> simp [h]
  · right; right; ext i; fin_cases i <;> simp [h]

end

section

/-! The first valuation ball has volume equal to the residue cardinality. -/

open _root_.MeasureTheory IsLocalRing
open scoped ENNReal

variable {R F : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F]

def residueLift (a : ResidueField R) : R := (residue_surjective a).choose

lemma residue_residueLift (a : ResidueField R) : residue R (residueLift a) = a :=
  (residue_surjective a).choose_spec

def integralBall (π : R) : Set F :=
  {x | IntegralElement (R := R) (algebraMap R F π * x)}

def residueCoset (π : R) (a : ResidueField R) : Set F :=
  {x | IntegralElement (R := R)
    (x - algebraMap R F (residueLift a) / algebraMap R F π)}

lemma integralBall_eq_union (π : R) (hπ : Irreducible π) :
    integralBall (F := F) π = ⋃ a : ResidueField R, residueCoset (F := F) π a := by
  have hp := OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.uniformizer_map_ne_zero (K := F) hπ
  ext x
  constructor
  · rintro ⟨r, hr⟩
    apply Set.mem_iUnion.mpr
    refine ⟨residue R r, ?_⟩
    have hres : residue R (r - residueLift (residue R r)) = 0 := by
      rw [map_sub, residue_residueLift, sub_self]
    have hdiv : π ∣ r - residueLift (residue R r) := by
      rw [← Ideal.mem_span_singleton, ← hπ.maximalIdeal_eq]
      exact (residue_eq_zero_iff _).mp hres
    obtain ⟨t, ht⟩ := hdiv
    refine ⟨t, ?_⟩
    have hm := congrArg (algebraMap R F) ht
    rw [map_sub, map_mul, hr] at hm
    change algebraMap R F t = x - algebraMap R F (residueLift (residue R r)) /
      algebraMap R F π
    apply (mul_left_cancel₀ hp)
    rw [mul_sub, mul_div_cancel₀ _ hp]
    exact hm.symm
  · intro hx
    obtain ⟨a, t, ht⟩ := Set.mem_iUnion.mp hx
    refine ⟨π * t + residueLift a, ?_⟩
    rw [map_add, map_mul, ht, mul_sub, mul_div_cancel₀ _ hp, sub_add_cancel]

lemma residueCoset_disjoint (π : R) (hπ : Irreducible π) :
    Pairwise (fun a b => Disjoint (residueCoset (F := F) π a) (residueCoset π b)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  rintro x ⟨s, hs⟩ ⟨t, ht⟩
  have hp := OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.uniformizer_map_ne_zero (K := F) hπ
  have he : residueLift a - residueLift b = π * (t - s) := by
    apply IsFractionRing.injective R F
    rw [map_sub, map_mul, map_sub, ht, hs]
    field_simp
    ring
  have hr := congrArg (residue R) he
  have hz : residue R π = 0 := by
    apply (residue_eq_zero_iff π).mpr
    rw [hπ.maximalIdeal_eq]
    exact Ideal.subset_span (Set.mem_singleton π)
  rw [map_sub, residue_residueLift, residue_residueLift, map_mul, hz, zero_mul] at hr
  exact hab (sub_eq_zero.mp hr)

variable [MeasurableSpace F] [MeasurableAdd F] [MeasurableNeg F]

omit [IsFractionRing R F] in
lemma measurable_residueCoset (π : R) (a : ResidueField R)
    (hO : MeasurableSet (Set.range (algebraMap R F))) :
    MeasurableSet (residueCoset (F := F) π a) :=
  hO.preimage (measurable_id.sub_const _)

omit [IsFractionRing R F] [MeasurableNeg F] in
lemma measure_residueCoset (π : R) (a : ResidueField R)
    (μ : Measure F) [μ.IsAddLeftInvariant] :
    μ (residueCoset (F := F) π a) = μ (Set.range (algebraMap R F)) := by
  change μ ((fun x => x - algebraMap R F (residueLift a) / algebraMap R F π) ⁻¹'
    Set.range (algebraMap R F)) = _
  simpa only [sub_eq_add_neg, add_comm] using measure_preimage_add μ
      (-(algebraMap R F (residueLift a) / algebraMap R F π))
      (Set.range (algebraMap R F))

theorem measure_integralBall [Finite (ResidueField R)] (π : R) (hπ : Irreducible π)
    (μ : Measure F) [μ.IsAddLeftInvariant]
    (hO : MeasurableSet (Set.range (algebraMap R F)))
    (hvol : μ (Set.range (algebraMap R F)) = 1) :
    μ (integralBall (F := F) π) = Nat.card (ResidueField R) := by
  let := Fintype.ofFinite (ResidueField R)
  rw [integralBall_eq_union π hπ,
    measure_iUnion (residueCoset_disjoint π hπ) (fun a => measurable_residueCoset π a hO)]
  simp [measure_residueCoset, hvol, Nat.card_eq_fintype_card]

end

/-! Elementary iterated integrals used by the unipotent Satake transform. -/

open _root_.MeasureTheory
open scoped Classical

variable {F : Type*} [Field F] [MeasurableSpace F]
  [MeasurableAdd F] [MeasurableNeg F]

def complexVolume (μ : Measure F) (s : Set F) : ℂ := (μ.real s : ℂ)

omit [Field F] [MeasurableAdd F] [MeasurableNeg F] in
lemma integral_if_mem (μ : Measure F) (s : Set F) (hs : MeasurableSet s) (c : ℂ) :
    (∫ x, if x ∈ s then c else 0 ∂μ) = complexVolume μ s * c := by
  classical
  have h := integral_indicator_const (μ := μ) c hs
  simpa only [Set.indicator_apply, complexVolume, Complex.real_smul, smul_eq_mul] using h

lemma integral_translated_if (μ : Measure F) [μ.IsAddLeftInvariant]
    (s : Set F) (hs : MeasurableSet s) (c : F) :
    (∫ x, if x - c ∈ s then (1 : ℂ) else 0 ∂μ) = complexVolume μ s := by
  classical
  have hm : μ ((fun x => x - c) ⁻¹' s) = μ s := by
    simpa only [sub_eq_add_neg, add_comm] using measure_preimage_add μ (-c) s
  have hh := integral_if_mem μ ((fun x => x - c) ⁻¹' s)
    (hs.preimage (measurable_id.sub_const c)) 1
  simpa [complexVolume, measureReal_def, hm] using hh

omit [Field F] [MeasurableAdd F] [MeasurableNeg F] in
lemma integral_box (μ : Measure F) (A B C : Set F)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    (∫ x, ∫ z, ∫ y, if x ∈ A ∧ y ∈ B ∧ z ∈ C then (1 : ℂ) else 0 ∂μ ∂μ ∂μ) =
      complexVolume μ A * complexVolume μ B * complexVolume μ C := by
  classical
  have hy (x z : F) :
      (∫ y, if x ∈ A ∧ y ∈ B ∧ z ∈ C then (1 : ℂ) else 0 ∂μ) =
      if x ∈ A ∧ z ∈ C then complexVolume μ B else 0 := by
    by_cases hx : x ∈ A <;> by_cases hz : z ∈ C <;>
      simp [hx, hz, integral_if_mem μ B hB]
  simp_rw [hy]
  have hz (x : F) :
      (∫ z, if x ∈ A ∧ z ∈ C then complexVolume μ B else 0 ∂μ) =
      if x ∈ A then complexVolume μ C * complexVolume μ B else 0 := by
    by_cases hx : x ∈ A <;> simp [hx, integral_if_mem μ C hC]
  simp_rw [hz]
  rw [integral_if_mem μ A hA]
  ring

lemma integral_twisted_box (μ : Measure F) [μ.IsAddLeftInvariant] (A B C : Set F)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hBneg : ∀ x : F, -x ∈ B ↔ x ∈ B) :
    (∫ x, ∫ z, ∫ y, if x ∈ A ∧ x * z - y ∈ B ∧ z ∈ C then (1 : ℂ) else 0 ∂μ ∂μ ∂μ) =
      complexVolume μ A * complexVolume μ B * complexVolume μ C := by
  classical
  have hy (x z : F) :
      (∫ y, if x ∈ A ∧ x * z - y ∈ B ∧ z ∈ C then (1 : ℂ) else 0 ∂μ) =
      if x ∈ A ∧ z ∈ C then complexVolume μ B else 0 := by
    have hneg (y : F) : x * z - y ∈ B ↔ y - x * z ∈ B := by
      rw [← hBneg (y - x * z), neg_sub]
    simp_rw [hneg]
    by_cases hx : x ∈ A <;> by_cases hz : z ∈ C <;>
      simp [hx, hz, integral_translated_if μ B hB]
  simp_rw [hy]
  have hz (x : F) :
      (∫ z, if x ∈ A ∧ z ∈ C then complexVolume μ B else 0 ∂μ) =
      if x ∈ A then complexVolume μ C * complexVolume μ B else 0 := by
    by_cases hx : x ∈ A <;> simp [hx, integral_if_mem μ C hC]
  simp_rw [hz]
  rw [integral_if_mem μ A hA]
  ring

end

end OAI.RepresentationTheory.Hecke.CosetCalculusArithmeticMeasure
