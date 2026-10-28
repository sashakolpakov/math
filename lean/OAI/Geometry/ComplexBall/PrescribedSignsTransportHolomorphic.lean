import OAI.Geometry.ComplexBall.PrescribedSignsPeriodTransport

/-! # Prescribed Signs Transport Holomorphic -/

namespace OAI.Geometry.ComplexBall.PrescribedSignsTransportHolomorphic.Intrinsic

noncomputable section

section

open scoped Classical

lemma holomorphicFamily_transport {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (e : X ≃L[ℂ] Y) (O : Set PrescribedSignsB.BallChart) (r : ℕ)
    (P : PrescribedSignsB.BallChart → Submodule ℂ Y) (hp : PrescribedSignsB.HolomorphicFamily O r P) :
    PrescribedSignsB.HolomorphicFamily O r (fun z => (P z).comap e.toLinearMap) := by
  intro z hz
  obtain ⟨N, hN, hzN, hNO, f, hf, hspan⟩ := hp z hz
  refine ⟨N, hN, hzN, hNO, (fun j w => e.symm (f j w)), ?_, ?_⟩
  · intro j
    exact e.symm.differentiable.comp_differentiableOn (hf j)
  · intro w hw
    obtain ⟨hli, hs⟩ := hspan w hw
    refine ⟨hli.map' e.symm.toLinearMap (LinearMap.ker_eq_bot.mpr e.symm.injective), ?_⟩
    have hm := congrArg (Submodule.map e.symm.toLinearMap) hs
    rw [Submodule.map_span, ← Set.range_comp] at hm
    exact hm.trans ((P w).map_equiv_eq_comap_symm e.symm.toLinearEquiv)

/-- Use the norm transported from the embedding coordinates on a native tensor space. -/
abbrev coordinateNorm {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] (e : X ≃ₗ[ℂ] Y) :
    NormedAddCommGroup X := NormedAddCommGroup.induced X Y e e.injective

lemma holomorphicFamily_native {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (e : X ≃ₗ[ℂ] Y) (O : Set PrescribedSignsB.BallChart) (r : ℕ)
    (P : PrescribedSignsB.BallChart → Submodule ℂ Y) (hp : PrescribedSignsB.HolomorphicFamily O r P) :
    letI := coordinateNorm e
    letI := NormedSpace.induced ℂ X Y e
    PrescribedSignsB.HolomorphicFamily O r (fun z => (P z).comap e.toLinearMap) := by
  let := coordinateNorm e
  let := NormedSpace.induced ℂ X Y e
  let ei : X ≃ₗᵢ[ℂ] Y := { e with norm_map' := fun _ => rfl }
  exact holomorphicFamily_transport ei.toContinuousLinearEquiv O r P hp

end

section

open scoped Classical TensorProduct

variable {E Place : Type*} [Field E] [Algebra ℚ E] [NumberField E]
  [NumberField.IsCMField E] [Fintype Place]

def sumFirst : PrescribedSignsPeriodTransport.Intrinsic.SumTensor E →ₗ[ℚ] PrescribedSignsPeriodTransport.Intrinsic.LineTensor E :=
  (LinearMap.fst ℚ _ _).comp ((PrescribedSignsPeriodTransport.Intrinsic.sumReduction (E := E)).restrictScalars ℚ).toLinearMap

def sumSecond : PrescribedSignsPeriodTransport.Intrinsic.SumTensor E →ₗ[ℚ] PrescribedSignsPeriodTransport.Intrinsic.LineTensor E :=
  (LinearMap.snd ℚ _ _).comp ((PrescribedSignsPeriodTransport.Intrinsic.sumReduction (E := E)).restrictScalars ℚ).toLinearMap

def rationalSumForm (δ : E) (a : Fin 2 → E) (H : Matrix (Fin 3) (Fin 3) E) :
    LinearMap.BilinForm ℚ (PrescribedSignsPeriodTransport.Intrinsic.SumTensor E) :=
  (PrescribedSignsPeriodTransport.Intrinsic.rationalLineForm δ (a 0) H).compl₁₂ sumFirst sumFirst +
  (PrescribedSignsPeriodTransport.Intrinsic.rationalLineForm δ (a 1) H).compl₁₂ sumSecond sumSecond

omit [NumberField.IsCMField E] [Fintype Place] in
lemma sumCoordinates_components (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (PrescribedSignsPeriodTransport.Intrinsic.SumTensor E)) :
    PrescribedSignsPeriodTransport.Intrinsic.sumCoordinates σ hσ x =
      (PrescribedSignsPeriodTransport.Intrinsic.lineCoordinates σ hσ ((sumFirst (E := E)).baseChange ℂ x),
       PrescribedSignsPeriodTransport.Intrinsic.lineCoordinates σ hσ ((sumSecond (E := E)).baseChange ℂ x)) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, Prod.mk_add_mk]
  | tmul z v => simp [PrescribedSignsPeriodTransport.Intrinsic.sumCoordinates, sumFirst, sumSecond]

lemma bilin_baseChange_add {X : Type*} [AddCommGroup X] [Module ℚ X]
    (B C : LinearMap.BilinForm ℚ X) (x y : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification X) :
    (B + C).baseChange ℂ x y = B.baseChange ℂ x y + C.baseChange ℂ x y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']; abel
  | tmul z v =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']; abel
    | tmul w v' => simp [add_smul]

lemma sumForm_transport (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (δ : E) (a : Fin 2 → E) (hδ : NumberField.IsCMField.complexConj E δ = -δ)
    (ha : ∀ i, NumberField.IsCMField.complexConj E (a i) = a i)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (x y : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (PrescribedSignsPeriodTransport.Intrinsic.SumTensor E)) :
    (rationalSumForm δ a H).baseChange ℂ x y =
      PrescribedSignsPeriodTransport.Intrinsic.coordinateForm (PrescribedSignsB.matrixB σ H) (fun τ => σ τ (δ * a 0))
        (PrescribedSignsPeriodTransport.Intrinsic.sumCoordinates σ hσ x).1 (PrescribedSignsPeriodTransport.Intrinsic.sumCoordinates σ hσ y).1 +
      PrescribedSignsPeriodTransport.Intrinsic.coordinateForm (PrescribedSignsB.matrixB σ H) (fun τ => σ τ (δ * a 1))
        (PrescribedSignsPeriodTransport.Intrinsic.sumCoordinates σ hσ x).2 (PrescribedSignsPeriodTransport.Intrinsic.sumCoordinates σ hσ y).2 := by
  rw [rationalSumForm, bilin_baseChange_add, PrescribedSignsPeriodTransport.Intrinsic.baseChange_compl, PrescribedSignsPeriodTransport.Intrinsic.baseChange_compl,
    PrescribedSignsPeriodTransport.Intrinsic.lineForm_transport σ hσ δ (a 0) hδ (ha 0) H hH,
    PrescribedSignsPeriodTransport.Intrinsic.lineForm_transport σ hσ δ (a 1) hδ (ha 1) H hH,
    sumCoordinates_components σ hσ x, sumCoordinates_components σ hσ y]

lemma rationalSumForm_cross (δ : E) (a : Fin 2 → E)
    (H : Matrix (Fin 3) (Fin 3) E) (x y : PrescribedSignsPeriodTransport.Intrinsic.LineTensor E) :
    rationalSumForm δ a H (PrescribedSignsPeriodTransport.Intrinsic.sumReduction.symm (x, 0)) (PrescribedSignsPeriodTransport.Intrinsic.sumReduction.symm (0, y)) = 0 := by
  simp [rationalSumForm, sumFirst, sumSecond]

lemma sumPositivePeriod_transport (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (δ : E) (a : Fin 2 → E) (hδ : NumberField.IsCMField.complexConj E δ = -δ)
    (ha : ∀ i, NumberField.IsCMField.complexConj E (a i) = a i)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (r : ℕ) (P : Submodule ℂ (PrescribedSignsB.Ambient Place × PrescribedSignsB.Ambient Place))
    (hp : PrescribedSignsB.PositivePeriod r
      (fun x y => PrescribedSignsPeriodTransport.Intrinsic.coordinateForm (PrescribedSignsB.matrixB σ H) (fun τ => σ τ (δ * a 0)) x.1 y.1 +
        PrescribedSignsPeriodTransport.Intrinsic.coordinateForm (PrescribedSignsB.matrixB σ H) (fun τ => σ τ (δ * a 1)) x.2 y.2)
      (fun x => (PrescribedSignsB.realConj x.1, PrescribedSignsB.realConj x.2)) P) :
    PrescribedSignsB.PositivePeriod r (fun x y => (rationalSumForm δ a H).baseChange ℂ x y)
      (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation (PrescribedSignsPeriodTransport.Intrinsic.SumTensor E))
      (P.comap (PrescribedSignsPeriodTransport.Intrinsic.sumCoordinates σ hσ).toLinearMap) := by
  have ht := PrescribedSignsPeriodTransport.Intrinsic.positivePeriod_transport (PrescribedSignsPeriodTransport.Intrinsic.sumCoordinates σ hσ) r _ _
    (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation (PrescribedSignsPeriodTransport.Intrinsic.SumTensor E)) (PrescribedSignsPeriodTransport.Intrinsic.sumCoordinates_conjugation σ hσ) P hp
  have he : (fun x y => (rationalSumForm δ a H).baseChange ℂ x y) =
      (fun x y => PrescribedSignsPeriodTransport.Intrinsic.coordinateForm (PrescribedSignsB.matrixB σ H) (fun τ => σ τ (δ * a 0))
        (PrescribedSignsPeriodTransport.Intrinsic.sumCoordinates σ hσ x).1 (PrescribedSignsPeriodTransport.Intrinsic.sumCoordinates σ hσ y).1 +
      PrescribedSignsPeriodTransport.Intrinsic.coordinateForm (PrescribedSignsB.matrixB σ H) (fun τ => σ τ (δ * a 1))
        (PrescribedSignsPeriodTransport.Intrinsic.sumCoordinates σ hσ x).2 (PrescribedSignsPeriodTransport.Intrinsic.sumCoordinates σ hσ y).2) := by
    funext x y
    exact sumForm_transport σ hσ δ a hδ ha H hH x y
  rw [he]
  exact ht

end

open scoped Classical TensorProduct

variable {E : Type*} [Field E] [NumberField E] [NumberField.IsCMField E]

/-- The fixed coefficients really belong to the maximal totally real subfield. -/
def realLineCoefficient (a : E) (ha : NumberField.IsCMField.complexConj E a = a) :
    NumberField.maximalRealSubfield E :=
  ⟨a, (NumberField.IsCMField.complexConj_eq_self_iff E a).mp ha⟩

lemma realLineCoefficient_coe (a : E) (ha : NumberField.IsCMField.complexConj E a = a) :
    (realLineCoefficient a ha : E) = a := rfl

/-- The rational trace in the public theorem is exactly the further trace
of the manuscript's `E/F` trace. -/
lemma trace_through_real_subfield (q : E) :
    Algebra.trace ℚ (NumberField.maximalRealSubfield E)
      (Algebra.trace (NumberField.maximalRealSubfield E) E q) = Algebra.trace ℚ E q := by
  exact Algebra.trace_trace q

lemma lineForm_iterated_trace (δ a : E) (H : Matrix (Fin 3) (Fin 3) E)
    (v v' : PrescribedSignsPeriodTransport.Intrinsic.V E) (w w' : E) :
    PrescribedSignsPeriodTransport.Intrinsic.rationalLineForm δ a H (v ⊗ₜ[E] w) (v' ⊗ₜ[E] w') =
      Algebra.trace ℚ (NumberField.maximalRealSubfield E)
        (Algebra.trace (NumberField.maximalRealSubfield E) E
          (δ * (∑ j, ∑ k, v j * H j k * NumberField.IsCMField.complexConj E (v' k)) *
            (a * w * NumberField.IsCMField.complexConj E w'))) := by
  rw [trace_through_real_subfield, PrescribedSignsPeriodTransport.Intrinsic.rationalLineForm_tmul]

lemma sumForm_iterated_trace (δ : E) (a : Fin 2 → E) (H : Matrix (Fin 3) (Fin 3) E)
    (v v' : PrescribedSignsPeriodTransport.Intrinsic.V E) (w w' : E × E) :
    rationalSumForm δ a H (v ⊗ₜ[E] w) (v' ⊗ₜ[E] w') =
      Algebra.trace ℚ (NumberField.maximalRealSubfield E)
        (Algebra.trace (NumberField.maximalRealSubfield E) E
          (δ * (∑ j, ∑ k, v j * H j k * NumberField.IsCMField.complexConj E (v' k)) *
            (a 0 * w.1 * NumberField.IsCMField.complexConj E w'.1 +
             a 1 * w.2 * NumberField.IsCMField.complexConj E w'.2))) := by
  rw [trace_through_real_subfield]
  change PrescribedSignsPeriodTransport.Intrinsic.rationalLineForm δ (a 0) H (v ⊗ₜ[E] w.1) (v' ⊗ₜ[E] w'.1) +
    PrescribedSignsPeriodTransport.Intrinsic.rationalLineForm δ (a 1) H (v ⊗ₜ[E] w.2) (v' ⊗ₜ[E] w'.2) = _
  rw [PrescribedSignsPeriodTransport.Intrinsic.rationalLineForm_tmul, PrescribedSignsPeriodTransport.Intrinsic.rationalLineForm_tmul, ← map_add]
  congr 1
  ring

end

end OAI.Geometry.ComplexBall.PrescribedSignsTransportHolomorphic.Intrinsic
