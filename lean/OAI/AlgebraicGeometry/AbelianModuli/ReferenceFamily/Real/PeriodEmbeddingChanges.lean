import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.PeriodHodgeTransport
import Mathlib.Algebra.Star.Module

/-! # Period Embedding Changes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.PeriodEmbeddingChanges

noncomputable section

/-! A real change given independently at the selected CM embeddings
acts on each literal complex embedding summand by the specified map.
The conjugate summands follow from the real structure. -/

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped TensorProduct Classical

def conjugateVecEquiv (q : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec where
  toFun v := star (q (star v))
  invFun v := star (q.symm (star v))
  left_inv v := by simp only [star_star, q.symm_apply_apply]
  right_inv v := by simp only [star_star, q.apply_symm_apply]
  map_add' v w := by simp only [star_add, map_add]
  map_smul' c v := by simp only [star_smul, map_smul, star_star, RingHom.id_apply]

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (E : Type) [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {Place : Type*}
    (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective
      (fun p : Place × Bool => if p.2 then ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (e : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A ≃ₗ[ℚ] (Fin 3 → E))

def realConjugateSelectedCoordinate (p : Place) : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℝ] Geometry.ComplexBall.PrescribedSignsB.Vec :=
  (starLinearEquiv ℝ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℝ] Geometry.ComplexBall.PrescribedSignsB.Vec).toLinearMap.comp
    ((LinearMap.proj p).comp (PeriodHodgeTransport.realSelectedPeriodCoordinates A E σ hσ e))

theorem complexMarkedPeriodCoordinates_conjugate_selected
    (p : Place) (x : ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) :
    PeriodHodgeTransport.complexMarkedPeriodCoordinates A E e x (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p)) =
      (realConjugateSelectedCoordinate A E σ hσ e p).liftBaseChange ℂ
        (PeriodHodgeTransport.nativeTangentComplexification A x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul z x =>
    rw [PeriodHodgeTransport.complexMarkedPeriodCoordinates_tmul, PeriodHodgeTransport.nativeTangentComplexification_tmul]
    change z • (fun j => ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p) (e x j)) =
      z • star (PeriodHodgeTransport.realSelectedPeriodCoordinates A E σ hσ e x.val p)
    rw [PeriodHodgeTransport.realSelectedPeriodCoordinates_rational]
    rfl

theorem realPeriodComplexification_conjugate_selected
    (q : Place → Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (x : ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) (p : Place) :
    PeriodHodgeTransport.complexMarkedPeriodCoordinates A E e
        (PeriodHodgeTransport.realPeriodComplexification A (Intrinsic.MixedPeriodCoordinates.nativeMixedComponentChange E A σ hσ e q) x)
        (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p)) =
      conjugateVecEquiv (q p)
        (PeriodHodgeTransport.complexMarkedPeriodCoordinates A E e x (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p))) := by
  rw [complexMarkedPeriodCoordinates_conjugate_selected A E σ hσ e,
    PeriodHodgeTransport.realPeriodComplexification_coordinates,
    complexMarkedPeriodCoordinates_conjugate_selected A E σ hσ e]
  generalize PeriodHodgeTransport.nativeTangentComplexification A x = y
  induction y using TensorProduct.inductionOn with
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul z v =>
    rw [LinearEquiv.baseChange_tmul]
    change z • star (PeriodHodgeTransport.realSelectedPeriodCoordinates A E σ hσ e
      (Intrinsic.MixedPeriodCoordinates.nativeMixedComponentChange E A σ hσ e q v) p) =
      conjugateVecEquiv (q p) (z • star (PeriodHodgeTransport.realSelectedPeriodCoordinates A E σ hσ e v p))
    rw [(conjugateVecEquiv (q p)).map_smul]
    change z • star (PeriodHodgeTransport.realSelectedPeriodCoordinates A E σ hσ e
      (Intrinsic.MixedPeriodCoordinates.nativeMixedComponentChange E A σ hσ e q v) p) =
      z • star (q p (star (star (PeriodHodgeTransport.realSelectedPeriodCoordinates A E σ hσ e v p))))
    rw [star_star]
    exact congrArg (fun w : Geometry.ComplexBall.PrescribedSignsB.Vec => z • star w)
      (Intrinsic.MixedPeriodCoordinates.nativeMixedComponentChange_selected E A σ hσ e q v p)

omit [NumberField.IsCMField E] in
def complexEmbeddingInclusion (τ : E →ₐ[ℚ] ℂ) :
    Geometry.ComplexBall.PrescribedSignsB.Vec →ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :=
  (PeriodHodgeTransport.complexMarkedPeriodCoordinates A E e).symm.toLinearMap.comp
    (LinearMap.single ℂ (fun _ : E →ₐ[ℚ] ℂ => Geometry.ComplexBall.PrescribedSignsB.Vec) τ)

omit [NumberField.IsCMField E] in
theorem complexEmbeddingInclusion_coordinates (τ : E →ₐ[ℚ] ℂ) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    PeriodHodgeTransport.complexMarkedPeriodCoordinates A E e (complexEmbeddingInclusion A E e τ v) = Pi.single τ v :=
  (PeriodHodgeTransport.complexMarkedPeriodCoordinates A E e).apply_symm_apply _

theorem realPeriodComplexification_embedding
    (q : Place → Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (p : Place) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    PeriodHodgeTransport.realPeriodComplexification A (Intrinsic.MixedPeriodCoordinates.nativeMixedComponentChange E A σ hσ e q)
        (complexEmbeddingInclusion A E e (σ p) v) =
      complexEmbeddingInclusion A E e (σ p) (q p v) := by
  classical
  have hsel : Function.Injective σ := by
    intro i j hij
    have heq : (i, false) = (j, false) := hσ.injective hij
    exact congrArg Prod.fst heq
  have hconj (i : Place) : ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ i) ≠ σ p := by
    intro hij
    have heq : (i, true) = (p, false) := hσ.injective hij
    exact Bool.noConfusion (congrArg Prod.snd heq)
  apply (PeriodHodgeTransport.complexMarkedPeriodCoordinates A E e).injective
  funext τ
  obtain ⟨⟨i, c⟩, hτ⟩ := hσ.surjective τ
  cases c with
  | false =>
    change σ i = τ at hτ
    subst τ
    rw [PeriodHodgeTransport.realPeriodComplexification_selected A E σ hσ e,
      complexEmbeddingInclusion_coordinates, complexEmbeddingInclusion_coordinates]
    by_cases hip : i = p
    · subst i
      simp only [Pi.single_eq_same]
    · simp only [Pi.single_eq_of_ne (hsel.ne hip), map_zero]
  | true =>
    change ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ i) = τ at hτ
    subst τ
    rw [realPeriodComplexification_conjugate_selected A E σ hσ e,
      complexEmbeddingInclusion_coordinates, complexEmbeddingInclusion_coordinates]
    simp only [Pi.single_eq_of_ne (hconj i), map_zero]

omit [NumberField.IsCMField E] in
def fixedFirstComplexInclusion (τ : E →ₐ[ℚ] ℂ) (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) :
    Geometry.ComplexBall.PrescribedSignsB.Vec →ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification (Fin 3 → E) :=
  (RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates E).symm.toLinearMap.comp
    ((LinearMap.single ℂ (fun _ : E →ₐ[ℚ] ℂ => Geometry.ComplexBall.PrescribedSignsB.Vec) τ).comp e₀.toLinearMap)

omit [NumberField.IsCMField E] in
theorem fixedFirstComplexInclusion_native (τ : E →ₐ[ℚ] ℂ)
    (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    e.symm.toLinearMap.baseChange ℂ (fixedFirstComplexInclusion E τ e₀ v) =
      complexEmbeddingInclusion A E e τ (e₀ v) := rfl

theorem realChanged_firstKernel
    (q : Place → Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (p : Place)
    (e₀ r : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (hq : ∀ v, q p (e₀ v) = e₀ (r v)) (z w : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (hz : ∀ v, Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (complexEmbeddingInclusion A E e (σ p) (e₀ v)) = 0 ↔
      v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z})
    (hw : (Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z}).map r.toLinearMap =
      Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector w}) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    PeriodHodgeTransport.realChangedComplexPeriodMap A (Intrinsic.MixedPeriodCoordinates.nativeMixedComponentChange E A σ hσ e q)
        (e.symm.toLinearMap.baseChange ℂ (fixedFirstComplexInclusion E (σ p) e₀ v)) = 0 ↔
      v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector w} := by
  let U := PeriodHodgeTransport.realPeriodComplexification A (Intrinsic.MixedPeriodCoordinates.nativeMixedComponentChange E A σ hσ e q)
  have hu : U (complexEmbeddingInclusion A E e (σ p) (e₀ (r.symm v))) =
      complexEmbeddingInclusion A E e (σ p) (e₀ v) := by
    rw [realPeriodComplexification_embedding, hq, r.apply_symm_apply]
  have hi : U.symm (complexEmbeddingInclusion A E e (σ p) (e₀ v)) =
      complexEmbeddingInclusion A E e (σ p) (e₀ (r.symm v)) := by
    rw [← hu, U.symm_apply_apply]
  rw [fixedFirstComplexInclusion_native, PeriodHodgeTransport.realChangedComplexPeriodMap_factor, hi, hz,
    ← hw, Submodule.mem_map_equiv]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.PeriodEmbeddingChanges
