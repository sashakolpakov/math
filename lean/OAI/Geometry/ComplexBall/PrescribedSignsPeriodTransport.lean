import OAI.Geometry.ComplexBall.PrescribedSignsWeak
import OAI.AlgebraicGeometry.ComplexMultiplication.CM.TraceForm
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! # Prescribed Signs Period Transport -/

namespace OAI.Geometry.ComplexBall.PrescribedSignsPeriodTransport.Intrinsic

noncomputable section

section

open scoped Classical TensorProduct
open OAI.AlgebraicGeometry.ComplexMultiplication.CM.TraceForm

variable {E Place : Type*} [Field E] [Algebra ℚ E] [NumberField E]

abbrev V (E : Type*) := Fin 3 → E
abbrev LineTensor (E : Type*) [Field E] := V E ⊗[E] E
abbrev SumTensor (E : Type*) [Field E] := V E ⊗[E] (E × E)

def regroup (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1)) :
    (Fin 3 → (E →ₐ[ℚ] ℂ) → ℂ) ≃ₗ[ℂ] PrescribedSignsB.Ambient Place := by
  let e : Place × Bool ≃ (E →ₐ[ℚ] ℂ) := Equiv.ofBijective _ hσ
  refine {
    toFun := fun x τ => (fun j => x j (σ τ), fun j => x j (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ τ)))
    invFun := fun x j ρ => if (e.symm ρ).2 then (x (e.symm ρ).1).2 j else (x (e.symm ρ).1).1 j
    left_inv := ?_
    right_inv := ?_
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  · intro x
    funext j ρ
    have he : (if (e.symm ρ).2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ (e.symm ρ).1) else σ (e.symm ρ).1) = ρ := e.apply_symm_apply ρ
    dsimp only
    split_ifs at he ⊢ with hb
    · exact congrArg (x j) he
    · exact congrArg (x j) he
  · intro x
    funext τ
    have hfalse : e.symm (σ τ) = (τ, false) := e.symm_apply_apply (τ, false)
    have htrue : e.symm (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ τ)) = (τ, true) := e.symm_apply_apply (τ, true)
    apply Prod.ext <;> funext j <;> simp [hfalse, htrue]

def vectorCoordinates (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1)) :
    AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (V E) ≃ₗ[ℂ] PrescribedSignsB.Ambient Place :=
  (TensorProduct.piRight ℚ ℂ ℂ (fun _ : Fin 3 => E)) ≪≫ₗ
    (LinearEquiv.piCongrRight (fun _ => AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E)) ≪≫ₗ regroup σ hσ

lemma vectorCoordinates_tmul (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (z : ℂ) (x : V E) :
    vectorCoordinates σ hσ (z ⊗ₜ[ℚ] x) = z • PrescribedSignsB.embeddingCoordinates σ x := by
  ext τ j <;> exact AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv_tmul _ _ _ _

lemma vectorCoordinates_conjugation (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (V E)) :
    vectorCoordinates σ hσ (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation (V E) x) =
      PrescribedSignsB.realConj (vectorCoordinates σ hσ x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
      simp only [map_add, hx, hy]
      exact (PrescribedSignsB.realConjLinearMap Place).map_add _ _ |>.symm
  | tmul z x =>
      rw [AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation_tmul, vectorCoordinates_tmul, vectorCoordinates_tmul]
      ext τ j <;> simp [PrescribedSignsB.realConj, PrescribedSignsB.embeddingCoordinates, AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding_apply]

def lineReduction : LineTensor E ≃ₗ[E] V E := TensorProduct.rid E (V E)

def lineCoordinates (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1)) :
    AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (LineTensor E) ≃ₗ[ℂ] PrescribedSignsB.Ambient Place :=
  LinearEquiv.baseChange ℚ ℂ _ _ ((lineReduction (E := E)).restrictScalars ℚ) ≪≫ₗ vectorCoordinates σ hσ

lemma lineCoordinates_tmul (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (z : ℂ) (v : V E) (w : E) :
    lineCoordinates σ hσ (z ⊗ₜ[ℚ] (v ⊗ₜ[E] w)) =
      z • PrescribedSignsB.embeddingCoordinates σ (w • v) := by
  simp [lineCoordinates, lineReduction, vectorCoordinates_tmul]

lemma lineCoordinates_conjugation (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (LineTensor E)) :
    lineCoordinates σ hσ (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation (LineTensor E) x) =
      PrescribedSignsB.realConj (lineCoordinates σ hσ x) := by
  exact congrArg (vectorCoordinates σ hσ)
    (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.baseChange_coefficientConjugation ((lineReduction (E := E)).restrictScalars ℚ).toLinearMap x)
      |>.trans (vectorCoordinates_conjugation σ hσ _)

def sumReduction : SumTensor E ≃ₗ[E] LineTensor E × LineTensor E :=
  TensorProduct.prodRight E E (V E) E E

def sumCoordinates (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1)) :
    AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (SumTensor E) ≃ₗ[ℂ] PrescribedSignsB.Ambient Place × PrescribedSignsB.Ambient Place :=
  LinearEquiv.baseChange ℚ ℂ _ _ ((sumReduction (E := E)).restrictScalars ℚ) ≪≫ₗ
    TensorProduct.prodRight ℚ ℂ ℂ (LineTensor E) (LineTensor E) ≪≫ₗ
      (lineCoordinates σ hσ).prodCongr (lineCoordinates σ hσ)

lemma sumCoordinates_tmul (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (z : ℂ) (v : V E) (w : E × E) :
    sumCoordinates σ hσ (z ⊗ₜ[ℚ] (v ⊗ₜ[E] w)) =
      (z • PrescribedSignsB.embeddingCoordinates σ (w.1 • v), z • PrescribedSignsB.embeddingCoordinates σ (w.2 • v)) := by
  simp [sumCoordinates, sumReduction, lineCoordinates_tmul]

lemma sumCoordinates_conjugation (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (SumTensor E)) :
    sumCoordinates σ hσ (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation (SumTensor E) x) =
      (PrescribedSignsB.realConj (sumCoordinates σ hσ x).1, PrescribedSignsB.realConj (sumCoordinates σ hσ x).2) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
      simp only [map_add, hx, hy, Prod.fst_add, Prod.snd_add]
      exact Prod.ext ((PrescribedSignsB.realConjLinearMap Place).map_add _ _).symm
        ((PrescribedSignsB.realConjLinearMap Place).map_add _ _).symm
  | tmul z v =>
      simp only [AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation_tmul, sumCoordinates,
        LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
        TensorProduct.prodRight_tmul, LinearEquiv.prodCongr_apply]
      apply Prod.ext
      · simpa only [AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation_tmul] using
          (lineCoordinates_conjugation σ hσ (z ⊗ₜ[ℚ] (((sumReduction (E := E)).restrictScalars ℚ) v).1))
      · simpa only [AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation_tmul] using
          (lineCoordinates_conjugation σ hσ (z ⊗ₜ[ℚ] (((sumReduction (E := E)).restrictScalars ℚ) v).2))

end

section

open scoped Classical TensorProduct
open OAI.AlgebraicGeometry.ComplexMultiplication.CM.TraceForm

variable {E Place : Type*} [Field E] [Algebra ℚ E] [NumberField E]
  [NumberField.IsCMField E] [Fintype Place]

def rationalVectorForm (δ a : E) (H : Matrix (Fin 3) (Fin 3) E) :
    LinearMap.BilinForm ℚ (V E) :=
  ∑ j, ∑ k, (AlgebraicGeometry.ComplexMultiplication.CM.TraceForm.cmTracePairing E (δ * a * H j k)).flip.compl₁₂
    (LinearMap.proj j) (LinearMap.proj k)

lemma rationalVectorForm_apply (δ a : E) (H : Matrix (Fin 3) (Fin 3) E) (x y : V E) :
    rationalVectorForm δ a H x y = Algebra.trace ℚ E
      (δ * a * (∑ j, ∑ k, x j * H j k * NumberField.IsCMField.complexConj E (y k))) := by
  simp only [rationalVectorForm, LinearMap.sum_apply, LinearMap.compl₁₂_apply,
    LinearMap.proj_apply, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  change Algebra.trace ℚ E (δ * a * H j k * NumberField.IsCMField.complexConj E (y k) * x j) = _
  congr 1
  ring

def coordinateForm (B : Place → PrescribedSignsB.Bilin) (t : Place → ℂ) :
    LinearMap.BilinForm ℂ (PrescribedSignsB.Ambient Place) :=
  ∑ τ, t τ •
    ((B τ).compl₁₂
      ((LinearMap.fst ℂ PrescribedSignsB.Vec PrescribedSignsB.Vec).comp (LinearMap.proj τ))
      ((LinearMap.snd ℂ PrescribedSignsB.Vec PrescribedSignsB.Vec).comp (LinearMap.proj τ)) -
    (B τ).flip.compl₁₂
      ((LinearMap.snd ℂ PrescribedSignsB.Vec PrescribedSignsB.Vec).comp (LinearMap.proj τ))
      ((LinearMap.fst ℂ PrescribedSignsB.Vec PrescribedSignsB.Vec).comp (LinearMap.proj τ)))

lemma coordinateForm_apply (B : Place → PrescribedSignsB.Bilin) (t : Place → ℂ) (x y : PrescribedSignsB.Ambient Place) :
    coordinateForm B t x y = PrescribedSignsB.tracePairing (fun τ u v => B τ u v) t x y := by
  simp [coordinateForm, PrescribedSignsB.tracePairing]

lemma vectorForm_transport (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (δ a : E) (hδ : NumberField.IsCMField.complexConj E δ = -δ)
    (ha : NumberField.IsCMField.complexConj E a = a)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (x y : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (V E)) :
    (rationalVectorForm δ a H).baseChange ℂ x y =
      coordinateForm (PrescribedSignsB.matrixB σ H) (fun τ => σ τ (δ * a))
        (vectorCoordinates σ hσ x) (vectorCoordinates σ hσ y) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul z v =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul w v' =>
      rw [LinearMap.BilinForm.baseChange_tmul, vectorCoordinates_tmul, vectorCoordinates_tmul]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [coordinateForm_apply]
      have he : (fun τ u v => PrescribedSignsB.matrixB σ H τ u v) = PrescribedSignsB.localB σ H := by
        funext τ u v
        exact PrescribedSignsB.matrixB_apply σ H τ u v
      rw [he, PrescribedSignsB.tracePairing_rational σ hσ δ a hδ ha H hH, rationalVectorForm_apply]
      simp only [Algebra.smul_def]
      change (↑(Algebra.trace ℚ E (δ * a * (∑ j, ∑ k, v j * H j k * NumberField.IsCMField.complexConj E (v' k)))) : ℂ) * (z * w) = _
      ring

def rationalLineForm (δ a : E) (H : Matrix (Fin 3) (Fin 3) E) :
    LinearMap.BilinForm ℚ (LineTensor E) :=
  (rationalVectorForm δ a H).compl₁₂
    ((lineReduction (E := E)).restrictScalars ℚ).toLinearMap
    ((lineReduction (E := E)).restrictScalars ℚ).toLinearMap

lemma baseChange_compl {X Y : Type*} [AddCommGroup X] [Module ℚ X]
    [AddCommGroup Y] [Module ℚ Y] (B : LinearMap.BilinForm ℚ Y) (f : X →ₗ[ℚ] Y)
    (x y : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification X) :
    LinearMap.BilinForm.baseChange ℂ (B.compl₁₂ f f) x y =
      B.baseChange ℂ (f.baseChange ℂ x) (f.baseChange ℂ y) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul z v =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul w v' => simp

lemma lineForm_transport (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (δ a : E) (hδ : NumberField.IsCMField.complexConj E δ = -δ)
    (ha : NumberField.IsCMField.complexConj E a = a)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (x y : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (LineTensor E)) :
    (rationalLineForm δ a H).baseChange ℂ x y =
      coordinateForm (PrescribedSignsB.matrixB σ H) (fun τ => σ τ (δ * a))
        (lineCoordinates σ hσ x) (lineCoordinates σ hσ y) := by
  rw [rationalLineForm, baseChange_compl]
  exact vectorForm_transport σ hσ δ a hδ ha H hH _ _

lemma rationalLineForm_tmul (δ a : E) (H : Matrix (Fin 3) (Fin 3) E)
    (v v' : V E) (w w' : E) :
    rationalLineForm δ a H (v ⊗ₜ[E] w) (v' ⊗ₜ[E] w') =
      Algebra.trace ℚ E (δ *
        (∑ j, ∑ k, v j * H j k * NumberField.IsCMField.complexConj E (v' k)) *
        (a * w * NumberField.IsCMField.complexConj E w')) := by
  rw [rationalLineForm, LinearMap.compl₁₂_apply, rationalVectorForm_apply]
  change Algebra.trace ℚ E (δ * a * (∑ j, ∑ k, (w * v j) * H j k * NumberField.IsCMField.complexConj E (w' * v' k))) = _
  congr 1
  simp only [map_mul]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

end

section

open scoped Classical TensorProduct
open OAI.AlgebraicGeometry.ComplexMultiplication.CM.TraceForm

lemma positivePeriod_transport {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (e : X ≃ₗ[ℂ] Y) (r : ℕ) (ψ : Y → Y → ℂ) (κ : Y → Y)
    (κX : X → X) (hc : ∀ x, e (κX x) = κ (e x))
    (P : Submodule ℂ Y) (h : PrescribedSignsB.PositivePeriod r ψ κ P) :
    PrescribedSignsB.PositivePeriod r (fun x y => ψ (e x) (e y)) κX (P.comap e.toLinearMap) := by
  have hm : (P.comap e.toLinearMap).map e.toLinearMap = P := by
    exact Submodule.map_comap_eq_of_surjective e.surjective P
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (e.ofSubmodule' P).finrank_eq.trans h.1
  · exact (Submodule.Quotient.equiv _ _ e hm).finrank_eq.trans h.2.1
  · intro u hu v hv
    exact h.2.2.1 (e u) hu (e v) hv
  · intro u hu hne
    dsimp only
    rw [hc]
    exact h.2.2.2.1 (e u) hu (fun he => hne (e.injective (he.trans e.map_zero.symm)))
  · intro x
    obtain ⟨uv, huv, huniq⟩ := h.2.2.2.2 (e x)
    refine ⟨(e.symm uv.1, e.symm uv.2), ⟨?_, ?_, ?_⟩, ?_⟩
    · simpa only [Submodule.mem_comap, LinearEquiv.coe_coe, e.apply_symm_apply] using huv.1
    · simpa only [Submodule.mem_comap, LinearEquiv.coe_coe, e.apply_symm_apply] using huv.2.1
    · apply e.injective
      simpa only [map_add, hc, e.apply_symm_apply] using huv.2.2
    · intro ab hab
      have he : (e ab.1, e ab.2) = uv := huniq _ ⟨hab.1, hab.2.1, by
        rw [hab.2.2, map_add, hc]⟩
      exact Prod.ext (e.eq_symm_apply.mpr (congrArg Prod.fst he))
        (e.eq_symm_apply.mpr (congrArg Prod.snd he))

lemma linePositivePeriod_transport
    {E Place : Type*} [Field E] [Algebra ℚ E] [NumberField E]
    [NumberField.IsCMField E] [Fintype Place]
    (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (δ a : E) (hδ : NumberField.IsCMField.complexConj E δ = -δ)
    (ha : NumberField.IsCMField.complexConj E a = a)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (r : ℕ) (P : Submodule ℂ (PrescribedSignsB.Ambient Place))
    (hp : PrescribedSignsB.PositivePeriod r
      (fun x y => coordinateForm (PrescribedSignsB.matrixB σ H) (fun τ => σ τ (δ * a)) x y)
      PrescribedSignsB.realConj P) :
    PrescribedSignsB.PositivePeriod r (fun x y => (rationalLineForm δ a H).baseChange ℂ x y)
      (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation (LineTensor E))
      (P.comap (lineCoordinates σ hσ).toLinearMap) := by
  have ht := positivePeriod_transport (lineCoordinates σ hσ) r _ PrescribedSignsB.realConj
    (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation (LineTensor E)) (lineCoordinates_conjugation σ hσ) P hp
  have he : (fun x y => (rationalLineForm δ a H).baseChange ℂ x y) =
      (fun x y => coordinateForm (PrescribedSignsB.matrixB σ H) (fun τ => σ τ (δ * a))
        (lineCoordinates σ hσ x) (lineCoordinates σ hσ y)) := by
    funext x y
    exact lineForm_transport σ hσ δ a hδ ha H hH x y
  rw [he]
  exact ht

end

section

open scoped Classical

/-- The homology complex structure acts by `-i` on the filtration and by
`i` on its conjugate. Its Riemann form therefore has the opposite sign to
our positive-period trace form. -/
lemma riemannForm_sign {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (ψ : LinearMap.BilinForm ℂ Y) (u v : Y)
    (hu : ψ u u = 0) (hv : ψ v v = 0) (hskew : ψ v u = -ψ u v)
    (hpos : 0 < (ψ u v / Complex.I).re) :
    0 < (-ψ (u + v) ((-Complex.I) • u + Complex.I • v)).re := by
  have he : -ψ (u + v) ((-Complex.I) • u + Complex.I • v) =
      2 * (ψ u v / Complex.I) := by
    simp only [map_add, LinearMap.add_apply, map_smul, hu, hv, hskew, smul_eq_mul]
    simp only [div_eq_mul_inv, Complex.inv_I]
    ring
  rw [he]
  simpa using mul_pos (by norm_num : (0 : ℝ) < 2) hpos

lemma homologyComplexStructure_quotient {Y : Type*}
    [AddCommGroup Y] [Module ℂ Y] (P : Submodule ℂ Y)
    (u v : Y) (hu : u ∈ P) :
    P.mkQ ((-Complex.I) • u + Complex.I • v) = Complex.I • P.mkQ (u + v) := by
  have hz : P.mkQ u = 0 := (Submodule.Quotient.mk_eq_zero P).mpr hu
  simp only [map_add, map_smul, hz, smul_zero, zero_add]

end

open scoped Classical TensorProduct
open OAI.AlgebraicGeometry.ComplexMultiplication.CM.TraceForm

lemma baseChange_conjugation {X : Type*} [AddCommGroup X] [Module ℚ X]
    (B : LinearMap.BilinForm ℚ X) (x y : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification X) :
    B.baseChange ℂ (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation X x) (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation X y) =
      star (B.baseChange ℂ x y) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', star_add]
  | tmul z v =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy', star_add]
    | tmul w v' => simp [Algebra.smul_def]

lemma coordinateForm_skew {Place : Type*} [Fintype Place]
    (B : Place → PrescribedSignsB.Bilin) (t : Place → ℂ) (x y : PrescribedSignsB.Ambient Place) :
    coordinateForm B t y x = -coordinateForm B t x y := by
  simp only [coordinateForm_apply, PrescribedSignsB.tracePairing, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro τ _
  ring

/-- For a real vector written as `u + conjugate u`, the quotient complex
structure has the sign prescribed by `homologyComplexStructure_quotient`.
The negative rational trace form is strictly positive in that direction. -/
lemma rational_riemann_positive {X : Type*} [AddCommGroup X] [Module ℚ X]
    (B : LinearMap.BilinForm ℚ X)
    (hskew : ∀ x y : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification X, B.baseChange ℂ y x = -B.baseChange ℂ x y)
    (r : ℕ) (P : Submodule ℂ (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification X))
    (hp : PrescribedSignsB.PositivePeriod r (fun x y => B.baseChange ℂ x y) (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation X) P)
    (u : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification X) (hu : u ∈ P) (hne : u ≠ 0) :
    let v := AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation X u
    0 < (-B.baseChange ℂ (u + v) ((-Complex.I) • u + Complex.I • v)).re := by
  apply riemannForm_sign (B.baseChange ℂ) u (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation X u)
  · exact hp.2.2.1 u hu u hu
  · have huu : B.baseChange ℂ u u = 0 := hp.2.2.1 u hu u hu
    rw [baseChange_conjugation, huu, star_zero]
  · exact hskew _ _
  · exact (hp.2.2.2.1 u hu hne).2

lemma realVector_period_split {X : Type*} [AddCommGroup X] [Module ℚ X]
    (ψ : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification X → AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification X → ℂ)
    (r : ℕ) (P : Submodule ℂ (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification X))
    (hp : PrescribedSignsB.PositivePeriod r ψ (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation X) P)
    (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification X) (hx : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation X x = x) (hne : x ≠ 0) :
    ∃ u ∈ P, u ≠ 0 ∧ x = u + AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation X u := by
  obtain ⟨⟨u,v⟩, ⟨hu,hv,he⟩, hun⟩ := hp.2.2.2.2 x
  have hs : x = v + AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation X u := by
    calc
      x = AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation X x := hx.symm
      _ = AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation X (u + AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation X v) := congrArg _ he
      _ = v + AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation X u := by
        rw [map_add, AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive, add_comm]
  have heq : (v,u) = (u,v) := hun _ ⟨hv, hu, hs⟩
  have hvu : v = u := congrArg Prod.fst heq
  subst v
  refine ⟨u, hu, ?_, he⟩
  intro hz
  apply hne
  simpa only [hz, map_zero, add_zero] using he

lemma homologyJ_real {X : Type*} [AddCommGroup X] [Module ℚ X]
    (u : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification X) :
    AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation X ((-Complex.I) • u + Complex.I • AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation X u) =
      (-Complex.I) • u + Complex.I • AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation X u := by
  simp only [map_add, AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.coefficientConjugation_smul, star_neg, Complex.star_def,
    Complex.conj_I, neg_neg, AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive]
  exact add_comm _ _

lemma rationalRiemann_on_real {X : Type*} [AddCommGroup X] [Module ℚ X]
    (B : LinearMap.BilinForm ℚ X)
    (hskew : ∀ x y : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification X, B.baseChange ℂ y x = -B.baseChange ℂ x y)
    (r : ℕ) (P : Submodule ℂ (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification X))
    (hp : PrescribedSignsB.PositivePeriod r (fun x y => B.baseChange ℂ x y) (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation X) P)
    (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification X) (hx : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation X x = x) (hne : x ≠ 0) :
    ∃ j : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification X, AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation X j = j ∧
      P.mkQ j = Complex.I • P.mkQ x ∧ 0 < (-B.baseChange ℂ x j).re := by
  obtain ⟨u, hu, hune, rfl⟩ := realVector_period_split _ r P hp x hx hne
  exact ⟨(-Complex.I) • u + Complex.I • AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation X u,
    homologyJ_real u, homologyComplexStructure_quotient P u _ hu,
    rational_riemann_positive B hskew r P hp u hu hune⟩

lemma lineForm_skew
    {E Place : Type*} [Field E] [Algebra ℚ E] [NumberField E]
    [NumberField.IsCMField E] [Fintype Place]
    (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (δ a : E) (hδ : NumberField.IsCMField.complexConj E δ = -δ)
    (ha : NumberField.IsCMField.complexConj E a = a)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (x y : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (LineTensor E)) :
    (rationalLineForm δ a H).baseChange ℂ y x =
      -(rationalLineForm δ a H).baseChange ℂ x y := by
  rw [lineForm_transport σ hσ δ a hδ ha H hH y x,
    lineForm_transport σ hσ δ a hδ ha H hH x y]
  exact coordinateForm_skew _ _ _ _

end

end OAI.Geometry.ComplexBall.PrescribedSignsPeriodTransport.Intrinsic
