import OAI.RepresentationTheory.Hecke.RadialDilation.Archimedean

/-! # Complexification -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.Complexification.Realization

noncomputable section

section

/-! Realization of the paired embedding coordinates by rational complexification. -/

open scoped Classical TensorProduct

def flipFunctions (A B : Type*) :
    (A → B → ℂ) ≃ₗ[ℂ] (B → A → ℂ) where
  toFun f b a := f a b
  invFun f a b := f b a
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def pairingEmbeddings {E Place : Type*} [Field E] [Algebra ℚ E]
    (σ : Place → E →ₐ[ℚ] ℂ) : Place × Bool → (E →ₐ[ℚ] ℂ) :=
  fun p => if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1

def pairedFunctionEquiv {E Place : Type*} [Field E] [Algebra ℚ E]
    (σ : Place → E →ₐ[ℚ] ℂ) (hσ : Function.Bijective (pairingEmbeddings σ)) :
    ((E →ₐ[ℚ] ℂ) → Geometry.ComplexBall.PrescribedSignsB.Vec) ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Ambient Place := by
  let e := Equiv.ofBijective (pairingEmbeddings σ) hσ
  refine
    { toFun := fun f τ => (f (σ τ), f (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ τ)))
      invFun := fun u ρ => if (e.symm ρ).2 then (u (e.symm ρ).1).2 else (u (e.symm ρ).1).1
      left_inv := ?_
      right_inv := ?_
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  · intro f
    funext ρ
    obtain ⟨⟨τ, b⟩, rfl⟩ := e.surjective ρ
    dsimp only
    rw [e.symm_apply_apply]
    cases b <;> rfl
  · intro u
    funext τ
    have hp : e.symm (σ τ) = (τ, false) := e.symm_apply_apply (τ, false)
    have hn : e.symm (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ τ)) = (τ, true) := e.symm_apply_apply (τ, true)
    simp only [hp, hn, Bool.false_eq_true, ↓reduceIte]

def pairedComplexification
    (E : Type*) [Field E] [NumberField E] [Algebra ℚ E]
    {Place : Type*} (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (pairingEmbeddings σ)) :
    AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (Fin 3 → E) ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Ambient Place :=
  (TensorProduct.piRight ℚ ℂ ℂ (fun _ : Fin 3 => E)).trans
    ((LinearEquiv.piCongrRight (fun _ : Fin 3 => AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E)).trans
      ((flipFunctions (Fin 3) (E →ₐ[ℚ] ℂ)).trans (pairedFunctionEquiv σ hσ)))

theorem pairedComplexification_tmul
    (E : Type*) [Field E] [NumberField E] [Algebra ℚ E]
    {Place : Type*} (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (pairingEmbeddings σ))
    (z : ℂ) (x : Fin 3 → E) :
    pairedComplexification E σ hσ (z ⊗ₜ[ℚ] x) = z • Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ x := by
  ext τ j <;>
    simp [pairedComplexification, flipFunctions, pairedFunctionEquiv,
      TensorProduct.piRightHom_tmul, Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates, smul_eq_mul]

def rationalScalarEnd
    (E : Type*) [Field E] [Algebra ℚ E] (r : E) :
    (Fin 3 → E) →ₗ[ℚ] (Fin 3 → E) where
  toFun x j := r * x j
  map_add' x y := by ext j; simp [mul_add]
  map_smul' a x := by ext j; simp [Algebra.smul_def, mul_left_comm]

def pairedScalarEnd {Place : Type*} (a : Place → ℂ) :
    Geometry.ComplexBall.PrescribedSignsB.Ambient Place →ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Ambient Place where
  toFun u τ := Archimedean.Realization.pairedScalar (a τ) (u τ)
  map_add' u v := by ext τ j <;> simp [Archimedean.Realization.pairedScalar, smul_add]
  map_smul' c u := by ext τ j <;> simp [Archimedean.Realization.pairedScalar, smul_smul, mul_comm]

/-- Rational multiplication by r becomes the computed paired central action. -/
theorem scalar_complexification_identification
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
    (r : Eˣ)
    (hr : (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    {Place : Type*} (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective (pairingEmbeddings σ))
    (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (Fin 3 → E)) :
    pairedComplexification E σ hσ ((rationalScalarEnd E (r : E)).baseChange ℂ x) =
      pairedScalarEnd (fun τ => σ τ (r : E)) (pairedComplexification E σ hσ x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul z x =>
      rw [LinearMap.baseChange_tmul, pairedComplexification_tmul,
        pairedComplexification_tmul, map_smul]
      congr 1
      funext τ
      exact Archimedean.Realization.embeddingCoordinates_scalar E r hr σ x τ

end

/-! A Galois field embedded in a coefficient field splits into its actual embedding coordinates. -/

open scoped Classical TensorProduct

variable (E K : Type*) [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
  [Field K] [Algebra ℚ K] [Algebra E K] [IsScalarTower ℚ E K]

theorem splitEmbedding_card : Fintype.card (E →ₐ[ℚ] K) = Module.finrank ℚ E := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (Normal.algHomEquivAut ℚ K E),
    IsGalois.card_aut_eq_finrank]

def splitEmbeddingBasis : Module.Basis (E →ₐ[ℚ] K) K (E →ₗ[ℚ] K) :=
  basisOfLinearIndependentOfCardEqFinrank' _ (linearIndependent_algHom_toLinearMap ℚ E K)
    (by rw [splitEmbedding_card E K, Module.finrank_linearMap_self])

theorem splitEmbeddingBasis_apply (σ : E →ₐ[ℚ] K) :
    splitEmbeddingBasis E K σ = σ.toLinearMap := by
  simp [splitEmbeddingBasis]

def splitDualBasis : Module.Basis (E →ₐ[ℚ] K) K (Module.Dual K (K ⊗[ℚ] E)) :=
  (splitEmbeddingBasis E K).map (LinearMap.liftBaseChangeEquiv K)

def splitFieldBaseChange : (K ⊗[ℚ] E) ≃ₗ[K] ((E →ₐ[ℚ] K) → K) :=
  (Module.evalEquiv K (K ⊗[ℚ] E)).trans (splitDualBasis E K).dualBasis.equivFun

theorem splitFieldBaseChange_apply (x : K ⊗[ℚ] E) (σ : E →ₐ[ℚ] K) :
    splitFieldBaseChange E K x σ = σ.toLinearMap.liftBaseChange K x := by
  simp [splitFieldBaseChange, Module.Basis.dualBasis_equivFun, splitDualBasis,
    splitEmbeddingBasis_apply]

theorem splitFieldBaseChange_tmul (z : K) (x : E) (σ : E →ₐ[ℚ] K) :
    splitFieldBaseChange E K (z ⊗ₜ[ℚ] x) σ = z * σ x := by
  rw [splitFieldBaseChange_apply]
  rfl

def splitRankThreeBaseChange : (K ⊗[ℚ] (Fin 3 → E)) ≃ₗ[K] ((E →ₐ[ℚ] K) → Fin 3 → K) :=
  (TensorProduct.piRight ℚ K K (fun _ : Fin 3 => E)).trans
    ((LinearEquiv.piCongrRight (fun _ : Fin 3 => splitFieldBaseChange E K)).trans
      { toFun := fun f σ i => f i σ
        invFun := fun f i σ => f σ i
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl })

theorem splitRankThreeBaseChange_tmul (z : K) (x : Fin 3 → E) (σ : E →ₐ[ℚ] K) (i : Fin 3) :
    splitRankThreeBaseChange E K (z ⊗ₜ[ℚ] x) σ i = z * σ (x i) := by
  simp [splitRankThreeBaseChange, TensorProduct.piRightHom_tmul, splitFieldBaseChange_tmul]

theorem splitRankThreeBaseChange_tmul_eq (z : K) (x : Fin 3 → E) :
    splitRankThreeBaseChange E K (z ⊗ₜ[ℚ] x) = z • (fun σ i => σ (x i)) := by
  funext σ i
  exact splitRankThreeBaseChange_tmul E K z x σ i

theorem splitRankThreeBaseChange_scalar (r : E) (x : K ⊗[ℚ] (Fin 3 → E)) (σ : E →ₐ[ℚ] K) :
    splitRankThreeBaseChange E K ((rationalScalarEnd E r).baseChange K x) σ =
      σ r • splitRankThreeBaseChange E K x σ := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, smul_add]
  | tmul z x =>
      funext i
      rw [LinearMap.baseChange_tmul, splitRankThreeBaseChange_tmul]
      change z * σ (r * x i) = σ r * splitRankThreeBaseChange E K (z ⊗ₜ[ℚ] x) σ i
      rw [splitRankThreeBaseChange_tmul, map_mul]
      ring

end

end OAI.RepresentationTheory.Hecke.RadialDilation.Complexification.Realization
