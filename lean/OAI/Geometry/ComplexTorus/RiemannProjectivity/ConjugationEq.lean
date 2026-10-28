import OAI.Geometry.ComplexTorus.RiemannProjectivity.PurePrimitiveEq
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation

/-! # Conjugation Eq -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.ConjugationEq.Constructions.Conjugation

noncomputable section

/-! # RiemannProjectivity: the conjugate Hodge type under the actual period comparison -/

open scoped _root_.NumberField TensorProduct

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction OAI.Geometry.ComplexTorus.RiemannProjectivity.ComparisonField.Constructions.HodgeComparison

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E)

def conjugateCovector (l : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] ℂ) : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] ℂ :=
  Complex.conjCLE.toContinuousLinearMap.comp l

omit [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] in
@[simp]
theorem conjugateCovector_apply (l : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] ℂ) (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) :
    conjugateCovector l z = star (l z) := rfl

omit [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] in
@[simp]
theorem conjugateCovector_involutive (l : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] ℂ) :
    conjugateCovector (conjugateCovector l) = l := by
  ext z
  exact star_star _

theorem fieldComplexCovector_conjugate_period (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification E) (a : 𝓞 E) :
    ComparisonField.Constructions.HodgeComparison.fieldComplexCovectorEquiv Φ (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation E x) (Φ.periodEmbedding (a : E)) =
      star (ComparisonField.Constructions.HodgeComparison.fieldComplexCovectorEquiv Φ x (Φ.periodEmbedding (a : E))) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, add_apply, star_add, hx, hy]
  | tmul c x =>
    simp only [AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation_tmul, ComparisonField.Constructions.HodgeComparison.fieldComplexCovectorEquiv_tmul, smul_apply,
      ComparisonField.Constructions.FieldComparison.fieldBettiEquiv_covector, smul_eq_mul, star_mul]
    simp [mul_comm]

theorem fieldComplexCovector_conjugation (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification E) :
    ComparisonField.Constructions.HodgeComparison.fieldComplexCovectorEquiv Φ (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation E x) =
      conjugateCovector (ComparisonField.Constructions.HodgeComparison.fieldComplexCovectorEquiv Φ x) := by
  let l := conjugateCovector (ComparisonField.Constructions.HodgeComparison.fieldComplexCovectorEquiv Φ x)
  let χ : Φ.periodIntegerLattice →+ ℂ :=
    l.toLinearMap.toAddMonoidHom.comp Φ.periodIntegerLattice.subtype.toAddMonoidHom
  have hl : ∀ t : Φ.periodIntegerLattice, l t = χ t := fun _ => rfl
  have hc : ∀ t : Φ.periodIntegerLattice,
      ComparisonField.Constructions.HodgeComparison.fieldComplexCovectorEquiv Φ (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation E x) t = χ t := by
    intro t
    obtain ⟨a, ha⟩ := (Φ.mem_periodIntegerLattice t).mp t.property
    change ComparisonField.Constructions.HodgeComparison.fieldComplexCovectorEquiv Φ (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation E x) t.val =
      star (ComparisonField.Constructions.HodgeComparison.fieldComplexCovectorEquiv Φ x t.val)
    rw [← ha, fieldComplexCovector_conjugate_period]
  exact (PrimitiveEq.Constructions.Primitive.exists_covector_extending_character Φ.periodIntegerLattice χ).unique hc hl

theorem fieldComplexCovector_antilinear_iff (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification E) :
    (∃ L : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℂ] ℂ,
      ComparisonField.Constructions.HodgeComparison.fieldComplexCovectorEquiv Φ x = conjugateCovector (L.restrictScalars ℝ)) ↔
    x ∈ Φ.hodgeStructure.antiholomorphic := by
  have htype : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation E x ∈ Φ.hodgeStructure.holomorphic ↔
      x ∈ Φ.hodgeStructure.antiholomorphic := by
    simpa only [AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive] using
      (Φ.hodgeStructure.conjugate_mem (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation E x)).symm
  rw [← htype, ← ComparisonField.Constructions.HodgeComparison.fieldComplexCovectorEquiv_complexLinear_iff, fieldComplexCovector_conjugation]
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨L, by rw [hL, conjugateCovector_involutive]⟩
  · rintro ⟨L, hL⟩
    exact ⟨L, by rw [← hL, conjugateCovector_involutive]⟩

theorem conjugateForm_hasBidegree {p q : ℕ}
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus (p + q))
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus p q a) :
    ∀ e ∈ atlas (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus, ∀ z ∈ e.target,
      ∀ (c : ℂˣ) (v : Fin (p + q) → AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E),
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus (p + q)).inChart
        e z (fun i => (c : ℂ) • v i) =
      star (Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q c) *
        (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus (p + q)).inChart
          e z v := by
  intro e he z hz c v
  have h := congrArg star (ha e he z hz c v)
  change star ((a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm _ _ (p + q)).inChart e z (fun i => (c : ℂ) • v i)) =
    star (Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q c) * star ((a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm _ _ (p + q)).inChart e z v)
  simpa only [star_mul, mul_comm] using h

theorem conjugate_antiholomorphic
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 0 1 a) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1 0 (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm a) := by
  intro e he z hz c v
  have h := conjugateForm_hasBidegree Φ (p := 0) (q := 1) a ha e he z hz c v
  simpa only [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_zero, pow_one, one_mul, mul_one, star_star] using h

theorem conjugate_invariant (l : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] ℂ) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm (FormsEq.Constructions.Forms.invariantClosedOneForm Φ l).val =
      (FormsEq.Constructions.Forms.invariantClosedOneForm Φ (conjugateCovector l)).val := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro z
  ext v
  rfl

theorem antiholomorphic_form_eq_invariant_mod_exact
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 0 1 a.val) :
    ∃ (L : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℂ] ℂ)
      (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 0),
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f =
        a.val - (FormsEq.Constructions.Forms.invariantClosedOneForm Φ (conjugateCovector (L.restrictScalars ℝ))).val := by
  obtain ⟨L, f, hf⟩ := PurePrimitiveEq.Constructions.PurePrimitive.holomorphic_form_eq_invariant_mod_exact Φ
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm a) (conjugate_antiholomorphic Φ a.val ha)
  refine ⟨L, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm f, ?_⟩
  rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.d_conjugateSmoothForm, hf]
  change AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothFormMap
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm a.val - (FormsEq.Constructions.Forms.invariantClosedOneForm Φ (L.restrictScalars ℝ)).val) = _
  rw [map_sub]
  exact congrArg₂ (· - ·) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm_involutive a.val)
    (conjugate_invariant Φ (L.restrictScalars ℝ))

theorem invariantH1_antiholomorphic_iff (l : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] ℂ) :
    (∃ a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1,
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 0 1 a.val ∧
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1 a = FormsEq.Constructions.Forms.invariantH1 Φ l) ↔
    ∃ L : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℂ] ℂ, l = conjugateCovector (L.restrictScalars ℝ) := by
  constructor
  · rintro ⟨a, ha, he⟩
    obtain ⟨L, f, hf⟩ := antiholomorphic_form_eq_invariant_mod_exact Φ a ha
    have hz : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1
        (a - FormsEq.Constructions.Forms.invariantClosedOneForm Φ (conjugateCovector (L.restrictScalars ℝ))) = 0 :=
      (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass_eq_zero_iff (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1 _).mpr ⟨f, hf⟩
    rw [map_sub, sub_eq_zero, he] at hz
    exact ⟨L, FormsEq.Constructions.Forms.invariantH1_injective Φ hz⟩
  · rintro ⟨L, rfl⟩
    refine ⟨FormsEq.Constructions.Forms.invariantClosedOneForm Φ (conjugateCovector (L.restrictScalars ℝ)), ?_, rfl⟩
    exact FormsEq.Constructions.Forms.invariantForm_hasBidegree Φ _ (Analysis.DifferentialForms.Manifold.Bidegree.conjugateLinearCovector_hasBidegree (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) L)

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.ConjugationEq.Constructions.Conjugation
