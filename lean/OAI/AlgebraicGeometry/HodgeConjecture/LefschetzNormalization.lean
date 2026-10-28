import OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType
import OAI.AlgebraicGeometry.ComplexMultiplication.KnownAlgebraicity
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Lefschetz Normalization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.LefschetzNormalization

noncomputable section

/-!
# LefschetzNormalization: normalization of the active embedding

The committed specification's binder `Σ` is reserved Lean syntax; here it is
named `reps`. The algebraicity predicates and their four interface hypotheses
are retained exactly. These already supply the uses of scalar descent and
degree-two/weight-one algebraicity, so the separately supplied ScalarDescent and DegreeTwo
propositions are not needed for this abstract normalization implication.
Identifying the predicates with geometric cycle-class images remains the
modeling obligation documented in the specification; no such identification
is asserted by this proof. No statement stub is imported or used.
-/

open scoped TensorProduct Classical
open OAI.AlgebraicGeometry.ComplexMultiplication.KnownAlgebraicity.CM OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]

abbrev G := Gal(E/ℚ)
abbrev Sign := ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : G E => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)
abbrev FourTypes := Fin 4 → Sign E

def switchLabels : Fin 4 → G E :=
  fun i => if i.val < 2 then 1 else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E

def embeddingGenerator (τ : G E) : ComplexMultiplication.WeightOne.CM.Complexification E :=
  ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ)

omit [IsGalois ℚ E] in
lemma conj_sq : ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E = 1 := by
  apply AlgEquiv.ext
  intro x
  exact ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_apply_apply E x

omit [IsGalois ℚ E] in
lemma conj_inv : (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)⁻¹ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E := by
  exact inv_eq_of_mul_eq_one_left (conj_sq E)

omit [IsGalois ℚ E] in
lemma sign_right_conj (v : Sign E) (τ : G E) :
    v.val (τ * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E) = !v.val τ := by
  rw [← (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_commute E τ).eq]
  exact v.property τ

def translate (v : Sign E) (g : G E) : Sign E :=
  ⟨fun σ => v.val (σ * g), fun σ => by
    simpa only [mul_assoc] using v.property (σ * g)⟩

omit [NumberField.IsCMField E] in
lemma coordinates_baseChange (f τ : G E) (x : ComplexMultiplication.WeightOne.CM.Complexification E) :
    ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E (f.toLinearMap.baseChange ℂ x)
        (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ) =
      ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E x (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E (τ * f)) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul z a => simp [LinearMap.baseChange_tmul, AlgEquiv.mul_apply]

omit [NumberField.IsCMField E] in
lemma embeddingGenerator_transport (g τ : G E) :
    (g⁻¹).toLinearMap.baseChange ℂ (embeddingGenerator E τ) =
      embeddingGenerator E (τ * g) := by
  apply (ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E).injective
  ext ρ
  obtain ⟨σ, rfl⟩ := (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E).surjective ρ
  rw [coordinates_baseChange]
  simp only [embeddingGenerator, ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv_embeddingVector]
  by_cases h : σ = τ * g
  · subst σ
    simp
  · have h' : τ ≠ σ * g⁻¹ := by
      intro he
      apply h
      rw [he, inv_mul_cancel_right]
    have h'' : τ * g ≠ σ := Ne.symm h
    simp [h', h'']

lemma translate_isHodgeMap (v : Sign E) (g : G E) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (translate E v g))
      (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v) (g⁻¹).toLinearMap := by
  intro x hx
  change x ∈ (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.embeddingType E (translate E v g)).subspace true at hx
  change (g⁻¹).toLinearMap.baseChange ℂ x ∈ (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.embeddingType E v).subspace true
  rw [ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType.mem_subspace_iff] at hx ⊢
  intro ρ hρ
  obtain ⟨τ, rfl⟩ := (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E).surjective ρ
  rw [coordinates_baseChange] at hρ
  have h := hx (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E (τ * g⁻¹)) hρ
  change (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.embeddingType E (translate E v g)).val
    (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E (τ * g⁻¹)) = true at h
  rw [ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.embeddingType_apply] at h
  change v.val ((τ * g⁻¹) * g) = true at h
  rw [ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.embeddingType_apply]
  simpa only [inv_mul_cancel_right] using h

lemma translate_inverse_isHodgeMap (v : Sign E) (g : G E) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v)
      (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (translate E v g)) g.toLinearMap := by
  have he : translate E (translate E v g) g⁻¹ = v := by
    apply Subtype.ext
    funext τ
    simp [translate]
  simpa only [he, inv_inv] using
    translate_isHodgeMap E (translate E v g) g⁻¹

omit [IsGalois ℚ E] in
lemma positive_representatives (s : ℕ)
    (hdegree : Fintype.card (G E) = 2 * s)
    (v : Sign E) (hv : v.val 1 = true) :
    ∃ reps : Finset (G E),
      (1 : G E) ∈ reps ∧
      (∀ τ : G E, τ ∈ reps ↔ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ ∉ reps) ∧
      reps.card = s := by
  let reps := Finset.univ.filter (fun τ : G E => v.val τ = true)
  let negs := Finset.univ.filter (fun τ : G E => ¬v.val τ = true)
  have hr (τ : G E) : τ ∈ reps ↔ v.val τ = true := by simp [reps]
  have hn (τ : G E) : τ ∈ negs ↔ ¬v.val τ = true := by simp [negs]
  have hc : reps.card = negs.card := by
    apply Finset.card_bij (fun τ _ => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)
    · intro τ hτ
      rw [hn, v.property, (hr τ).mp hτ]
      decide
    · intro τ _ ρ _ he
      exact mul_left_cancel he
    · intro τ hτ
      have ht : v.val τ = false := Bool.eq_false_iff.mpr ((hn τ).mp hτ)
      refine ⟨ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ, ?_, ?_⟩
      · rw [hr, v.property, ht]
        rfl
      · rw [← mul_assoc, conj_sq, one_mul]
  have hsum : reps.card + negs.card = Fintype.card (G E) :=
    Finset.card_filter_add_card_filter_not (fun τ : G E => v.val τ = true)
  refine ⟨reps, (hr 1).mpr hv, ?_, ?_⟩
  · intro τ
    rw [hr, hr, v.property]
    cases v.val τ <;> decide
  · omega

omit [IsGalois ℚ E] in
lemma group_eq_one_or_conj (reps : Finset (G E))
    (h1 : (1 : G E) ∈ reps)
    (hp : ∀ τ : G E, τ ∈ reps ↔ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ ∉ reps)
    (hc : reps.card = 1) (τ : G E) : τ = 1 ∨ τ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E := by
  have hs : reps = {1} := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    rw [ha] at h1
    have he : (1 : G E) = a := Finset.mem_singleton.mp h1
    simpa [← he] using ha
  by_cases ht : τ ∈ reps
  · left
    simpa [hs] using ht
  · right
    have hct : ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ ∈ reps := by
      by_contra hn
      exact ht ((hp τ).mpr hn)
    have he : ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ = 1 := by simpa [hs] using hct
    calc
      τ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) := by
        rw [← mul_assoc, conj_sq, one_mul]
      _ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E := by rw [he, mul_one]

omit [IsGalois ℚ E] in
lemma no_common_positive_opposite (u v : Sign E)
    (h : ¬∃ τ : G E, u.val τ = true ∧ v.val τ = true) (τ : G E) :
    v.val τ = !u.val τ := by
  have ht := fun hu hv => h ⟨τ, hu, hv⟩
  have hc := fun hu hv => h ⟨ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ, hu, hv⟩
  rw [u.property τ, v.property τ] at hc
  cases hu : u.val τ <;> cases hv : v.val τ <;> simp_all

lemma sign_pair_zero_iff (a b : Bool) :
    ComplexMultiplication.SignSwitch.CM.signValue a + ComplexMultiplication.SignSwitch.CM.signValue b = 0 ↔ b = !a := by
  cases a <;> cases b <;> norm_num [ComplexMultiplication.SignSwitch.CM.signValue]

lemma common_positive_of_balance (a b c d : Bool)
    (h : ComplexMultiplication.SignSwitch.CM.signValue a + ComplexMultiplication.SignSwitch.CM.signValue b = ComplexMultiplication.SignSwitch.CM.signValue c + ComplexMultiplication.SignSwitch.CM.signValue d)
    (ha : a = true) (hb : b = true) : c = true ∧ d = true := by
  subst a
  subst b
  cases c <;> cases d <;> norm_num [ComplexMultiplication.SignSwitch.CM.signValue] at *

section Inputs

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonObj

/-- The supplied ScalarDescent proposition, for rational spaces in the universe used here. -/
def ScalarTraceInput : Prop :=
  ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (V : Type) [AddCommGroup V] [Module ℚ V]
    (Hpq : Submodule ℂ (ComplexMultiplication.WeightOne.CM.Complexification V)) (t : K ⊗[ℚ] V),
    (∀ σ : K ≃ₐ[ℚ] K,
      ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K V (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K V σ t) ∈ Hpq) →
    t ∈ Submodule.span K {y : K ⊗[ℚ] V |
      ∃ v : V, y = (1 : K) ⊗ₜ[ℚ] v ∧ (1 : ℂ) ⊗ₜ[ℚ] v ∈ Hpq}

/-- The weight-one part of the supplied DegreeTwo specification. -/
def WeightOneInput : Prop :=
  ∀ (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (u : A.variety.rationalCohomology 1 →ₗ[ℚ] B.variety.rationalCohomology 1),
    (∀ x ∈ A.h1Holomorphic, u.baseChange ℂ x ∈ B.h1Holomorphic) →
    (∀ x ∈ A.h1Antiholomorphic, u.baseChange ℂ x ∈ B.h1Antiholomorphic) →
    ∃ n : ℕ, 0 < n ∧ ∃ g : B.toOver ⟶ A.toOver,
      IsMonHom g ∧ ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback g = (n : ℚ) • u

/-- The Albanese part of the supplied DegreeTwo specification. -/
def AlbaneseInput : Prop :=
  ∀ (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (x₀ : 𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver),
    ∃ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver)
      (eQ : A.variety.rationalCohomology 1 ≃ₗ[ℚ] X.rationalCohomology 1)
      (eC : A.variety.complexCohomology 1 ≃ₗ[ℂ] X.complexCohomology 1),
      x₀ ≫ a = η[A.toOver] ∧
      (∀ (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ B.toOver),
        x₀ ≫ f = η[B.toOver] →
          ∃! g : A.toOver ⟶ B.toOver, IsMonHom g ∧ a ≫ g = f) ∧
      eQ.toLinearMap = (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 a).hom ∧
      eC.toLinearMap = (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 a).hom ∧
      (A.variety.pureBettiSubspace 1 0).map eC.toLinearMap =
        X.pureBettiSubspace 1 0 ∧
      (A.variety.pureBettiSubspace 0 1).map eC.toLinearMap =
        X.pureBettiSubspace 0 1

/-- The degree-two part of the supplied DegreeTwo specification. -/
def DegreeTwoInput : Prop :=
  ∀ (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (α : V.rationalCohomology 2),
    V.IsRationalHodgeClass 1 α →
    ∃ z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle V 1, V.geometricCycleClassMap 1 z = α

end Inputs

/-- LefschetzNormalization with its original algebraicity interfaces and explicitly named graph inputs.
The leading underscores record that the graph inputs are unnecessary once the
specification's interface hypotheses are supplied. -/
theorem normalization_of_active_embedding
    (_hL2_2 : ScalarTraceInput)
    (_hP2_3_weight_one : WeightOneInput)
    (_hP2_3_albanese : AlbaneseInput)
    (_hP2_3_degree_two : DegreeTwoInput)
    (s : ℕ)
    (hdegree : Fintype.card (G E) = 2 * s)
    (A₂ : Sign E → Sign E → G E → G E → Prop)
    (A₄ : FourTypes E → (Fin 4 → G E) → Prop)
    (h11 :
      ∀ (u v : Sign E) (a b : G E),
        (∀ σ : G E,
          ComplexMultiplication.SignSwitch.CM.signValue (u.val (σ * a)) + ComplexMultiplication.SignSwitch.CM.signValue (v.val (σ * b)) = 0) →
        A₂ u v a b)
    (hproduct :
      ∀ (v : FourTypes E) (a : Fin 4 → G E) (p : Equiv.Perm (Fin 4)),
        A₂ (v (p 0)) (v (p 1)) (a (p 0)) (a (p 1)) →
        A₂ (v (p 2)) (v (p 3)) (a (p 2)) (a (p 3)) → A₄ v a)
    (hscalar :
      ∀ (v : FourTypes E) (a : Fin 4 → G E) (g : G E),
        A₄ v (fun i => g * a i) ↔ A₄ v a)
    (htransfer :
      ∀ (u v : FourTypes E) (a b : Fin 4 → G E)
        (f : Fin 4 → (E →ₗ[ℚ] E)),
        (∀ i, ComplexMultiplication.WeightOne.CM.IsHodgeMap (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (u i))
          (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)) (f i)) →
        (∀ i, (f i).baseChange ℂ (embeddingGenerator E (a i)) =
          embeddingGenerator E (b i)) → A₄ u a → A₄ v b)
    (v : FourTypes E)
    (hbalance : ∀ τ : G E,
      ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val τ) =
        ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val τ)) :
    ((¬ ∃ g : G E, (v 0).val g = true ∧ (v 1).val g = true) ∧
      (∀ τ : G E,
        (v 1).val τ = !((v 0).val τ) ∧
        (v 3).val τ = !((v 2).val τ)) ∧ A₄ v (switchLabels E))
    ∨
    (∃ (g : G E) (w : FourTypes E)
        (d : Fin 4 → G E → Bool) (reps : Finset (G E)),
      (∀ i σ, (w i).val σ = (v i).val (σ * g)) ∧
      (∀ i, (w i).val 1 = true) ∧
      (∀ τ : G E,
        ComplexMultiplication.SignSwitch.CM.signValue ((w 0).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((w 1).val τ) =
          ComplexMultiplication.SignSwitch.CM.signValue ((w 2).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((w 3).val τ)) ∧
      (∀ i, ComplexMultiplication.WeightOne.CM.IsHodgeMap (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (w i))
        (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)) (g⁻¹).toLinearMap) ∧
      (∀ τ : G E,
        (g⁻¹).toLinearMap.baseChange ℂ (embeddingGenerator E τ) =
          embeddingGenerator E (τ * g)) ∧
      (∀ i τ, d i τ = (w i).val τ⁻¹) ∧
      (∀ i τ, d i (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) = !(d i τ)) ∧
      (1 : G E) ∈ reps ∧
      (∀ τ : G E, τ ∈ reps ↔ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ ∉ reps) ∧
      reps.card = s ∧
      (A₄ w (switchLabels E) ↔ A₄ v (switchLabels E)) ∧
      ((s = 1 ∧ A₄ v (switchLabels E)) ∨ 2 ≤ s)) := by
  by_cases hpos : ∃ g : G E, (v 0).val g = true ∧ (v 1).val g = true
  · right
    obtain ⟨g, hg0, hg1⟩ := hpos
    obtain ⟨hg2, hg3⟩ := common_positive_of_balance _ _ _ _ (hbalance g) hg0 hg1
    let w : FourTypes E := fun i => translate E (v i) g
    have hw : ∀ i, (w i).val 1 = true := by
      intro i
      fin_cases i
      · change (v 0).val (1 * g) = true
        simpa only [one_mul] using hg0
      · change (v 1).val (1 * g) = true
        simpa only [one_mul] using hg1
      · change (v 2).val (1 * g) = true
        simpa only [one_mul] using hg2
      · change (v 3).val (1 * g) = true
        simpa only [one_mul] using hg3
    obtain ⟨reps, hrep1, hreppair, hrepcard⟩ :=
      positive_representatives E s hdegree (w 0) (hw 0)
    have hlabels : (fun i => switchLabels E i * g) =
        (fun i => g * switchLabels E i) := by
      funext i
      dsimp [switchLabels]
      split
      · simp
      · exact (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_commute E g).eq
    have hequiv : A₄ w (switchLabels E) ↔ A₄ v (switchLabels E) := by
      constructor
      · intro h
        have ht := htransfer w v (switchLabels E)
          (fun i => switchLabels E i * g) (fun _ => (g⁻¹).toLinearMap)
          (fun i => translate_isHodgeMap E (v i) g)
          (fun i => embeddingGenerator_transport E g (switchLabels E i)) h
        rw [hlabels] at ht
        exact (hscalar v (switchLabels E) g).mp ht
      · intro h
        have ht := (hscalar v (switchLabels E) g).mpr h
        rw [← hlabels] at ht
        apply htransfer v w (fun i => switchLabels E i * g)
          (switchLabels E) (fun _ => g.toLinearMap)
          (fun i => translate_inverse_isHodgeMap E (v i) g) _ ht
        intro i
        simpa only [inv_inv, mul_inv_cancel_right] using
          embeddingGenerator_transport E g⁻¹ (switchLabels E i * g)
    refine ⟨g, w, (fun i τ => (w i).val τ⁻¹), reps,
      (fun _ _ => rfl), hw, (fun τ => hbalance (τ * g)),
      (fun i => translate_isHodgeMap E (v i) g),
      embeddingGenerator_transport E g, (fun _ _ => rfl), ?_,
      hrep1, hreppair, hrepcard, hequiv, ?_⟩
    · intro i τ
      change (w i).val (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)⁻¹ = !(w i).val τ⁻¹
      rw [mul_inv_rev, conj_inv, sign_right_conj]
    · by_cases hs : s = 1
      · left
        refine ⟨hs, hequiv.mp ?_⟩
        have hsame (i j : Fin 4) (τ : G E) : (w i).val τ = (w j).val τ := by
          rcases group_eq_one_or_conj E reps hrep1 hreppair (hrepcard.trans hs) τ with
            ht | ht
          · rw [ht, hw i, hw j]
          · subst τ
            have hi := (w i).property 1
            have hj := (w j).property 1
            simp only [mul_one, hw i, hw j] at hi hj
            exact hi.trans hj.symm
        apply hproduct w (switchLabels E) (Equiv.swap (1 : Fin 4) 2)
        · change A₂ (w 0) (w 2) 1 (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)
          apply h11
          intro σ
          rw [mul_one, sign_right_conj, ComplexMultiplication.SignSwitch.CM.signValue_not, hsame 2 0 σ, add_neg_cancel]
        · change A₂ (w 1) (w 3) 1 (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)
          apply h11
          intro σ
          rw [mul_one, sign_right_conj, ComplexMultiplication.SignSwitch.CM.signValue_not, hsame 3 1 σ, add_neg_cancel]
      · right
        have hc : 0 < reps.card := Finset.card_pos.mpr ⟨1, hrep1⟩
        omega
  · left
    have hopp (τ : G E) :
        (v 1).val τ = !((v 0).val τ) ∧
        (v 3).val τ = !((v 2).val τ) := by
      have h01 := no_common_positive_opposite E (v 0) (v 1) hpos τ
      have hz := (sign_pair_zero_iff ((v 0).val τ) ((v 1).val τ)).mpr h01
      exact ⟨h01, (sign_pair_zero_iff _ _).mp ((hbalance τ).symm.trans hz)⟩
    refine ⟨hpos, hopp, ?_⟩
    apply hproduct v (switchLabels E) (Equiv.refl (Fin 4))
    · change A₂ (v 0) (v 1) 1 1
      apply h11
      intro σ
      simpa only [mul_one] using (sign_pair_zero_iff _ _).mpr (hopp σ).1
    · change A₂ (v 2) (v 3) (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E) (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)
      apply h11
      intro σ
      exact (sign_pair_zero_iff _ _).mpr (hopp (σ * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)).2

end

end OAI.AlgebraicGeometry.HodgeConjecture.LefschetzNormalization
