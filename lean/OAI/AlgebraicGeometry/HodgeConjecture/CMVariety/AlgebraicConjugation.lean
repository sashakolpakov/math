import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicForms
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.TorusRealManifold
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicPurePrimitive
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation

/-! # Algebraic Conjugation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicConjugation.CM.Abelian.Algebraization.Conjugation

noncomputable section

/-! # CMAbelianVariety: the conjugate Hodge type under the actual period comparison -/

open scoped _root_.NumberField TensorProduct

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicForms.CM.Abelian.Algebraization.Forms

variable (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData)

def conjugateCovector {Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData} (l : Φ.space →L[ℝ] ℂ) : Φ.space →L[ℝ] ℂ :=
  Complex.conjCLE.toContinuousLinearMap.comp l

@[simp]
theorem conjugateCovector_apply (l : Φ.space →L[ℝ] ℂ) (z : Φ.space) :
    conjugateCovector l z = star (l z) := rfl

@[simp]
theorem conjugateCovector_involutive (l : Φ.space →L[ℝ] ℂ) :
    conjugateCovector (conjugateCovector l) = l := by
  ext z
  exact star_star _

theorem conjugateForm_hasBidegree {p q : ℕ}
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Φ.space) Φ.periodTorus (p + q))
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (Φ.space) Φ.periodTorus p q a) :
    ∀ e ∈ atlas (Φ.space) Φ.periodTorus, ∀ z ∈ e.target,
      ∀ (c : ℂˣ) (v : Fin (p + q) → Φ.space),
      (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (Φ.space) Φ.periodTorus (p + q)).inChart
        e z (fun i => (c : ℂ) • v i) =
      star (Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q c) *
        (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (Φ.space) Φ.periodTorus (p + q)).inChart
          e z v := by
  intro e he z hz c v
  have h := congrArg star (ha e he z hz c v)
  change star ((a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm _ _ (p + q)).inChart e z (fun i => (c : ℂ) • v i)) =
    star (Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q c) * star ((a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm _ _ (p + q)).inChart e z v)
  simpa only [star_mul, mul_comm] using h

theorem conjugate_antiholomorphic
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Φ.space) Φ.periodTorus 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (Φ.space) Φ.periodTorus 0 1 a) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (Φ.space) Φ.periodTorus 1 0 (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm a) := by
  intro e he z hz c v
  have h := conjugateForm_hasBidegree Φ (p := 0) (q := 1) a ha e he z hz c v
  simpa only [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_zero, pow_one, one_mul, mul_one, star_star] using h

theorem conjugate_invariant (l : Φ.space →L[ℝ] ℂ) :
    ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm (AlgebraicForms.CM.Abelian.Algebraization.Forms.invariantClosedOneForm Φ l).val =
      (AlgebraicForms.CM.Abelian.Algebraization.Forms.invariantClosedOneForm Φ (conjugateCovector l)).val := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro z
  ext v
  rfl

theorem antiholomorphic_form_eq_invariant_mod_exact
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (Φ.space) Φ.periodTorus 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (Φ.space) Φ.periodTorus 0 1 a.val) :
    ∃ (L : Φ.space →L[ℂ] ℂ)
      (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Φ.space) Φ.periodTorus 0),
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f =
        a.val - (AlgebraicForms.CM.Abelian.Algebraization.Forms.invariantClosedOneForm Φ (conjugateCovector (L.restrictScalars ℝ))).val := by
  obtain ⟨L, f, hf⟩ := AlgebraicPurePrimitive.CM.Abelian.Algebraization.PurePrimitive.holomorphic_form_eq_invariant_mod_exact Φ
    (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm a) (conjugate_antiholomorphic Φ a.val ha)
  refine ⟨L, ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm f, ?_⟩
  rw [ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.d_conjugateSmoothForm, hf]
  change ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothFormMap
    (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm a.val - (AlgebraicForms.CM.Abelian.Algebraization.Forms.invariantClosedOneForm Φ (L.restrictScalars ℝ)).val) = _
  rw [map_sub]
  exact congrArg₂ (· - ·) (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm_involutive a.val)
    (conjugate_invariant Φ (L.restrictScalars ℝ))

theorem invariantH1_antiholomorphic_iff (l : Φ.space →L[ℝ] ℂ) :
    (∃ a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (Φ.space) Φ.periodTorus 1,
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (Φ.space) Φ.periodTorus 0 1 a.val ∧
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (Φ.space) Φ.periodTorus 1 a = AlgebraicForms.CM.Abelian.Algebraization.Forms.invariantH1 Φ l) ↔
    ∃ L : Φ.space →L[ℂ] ℂ, l = conjugateCovector (L.restrictScalars ℝ) := by
  constructor
  · rintro ⟨a, ha, he⟩
    obtain ⟨L, f, hf⟩ := antiholomorphic_form_eq_invariant_mod_exact Φ a ha
    have hz : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (Φ.space) Φ.periodTorus 1
        (a - AlgebraicForms.CM.Abelian.Algebraization.Forms.invariantClosedOneForm Φ (conjugateCovector (L.restrictScalars ℝ))) = 0 :=
      (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass_eq_zero_iff (Φ.space) Φ.periodTorus 1 _).mpr ⟨f, hf⟩
    rw [map_sub, sub_eq_zero, he] at hz
    exact ⟨L, AlgebraicForms.CM.Abelian.Algebraization.Forms.invariantH1_injective Φ hz⟩
  · rintro ⟨L, rfl⟩
    refine ⟨AlgebraicForms.CM.Abelian.Algebraization.Forms.invariantClosedOneForm Φ (conjugateCovector (L.restrictScalars ℝ)), ?_, rfl⟩
    exact AlgebraicForms.CM.Abelian.Algebraization.Forms.invariantForm_hasBidegree Φ _ (Analysis.DifferentialForms.Manifold.Bidegree.conjugateLinearCovector_hasBidegree (Φ.space) L)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicConjugation.CM.Abelian.Algebraization.Conjugation
