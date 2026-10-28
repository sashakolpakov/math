import OAI.RepresentationTheory.Weil.UnitarySplitting.TensorModelTopology
import OAI.RepresentationTheory.Weil.UnitarySplitting.QuadraticNorm

/-! # Tensor Frame Coordinates -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.TensorFrameCoordinates.Construction

noncomputable section

/-! Continuous tensor coordinates under matrix congruence and permutation. -/

open _root_.Matrix
open scoped Kronecker

theorem sesquilinear_reindex
    {F E I J : Type} [Field F] [Field E] [Algebra F E]
    [Fintype I] [Fintype J] (σ : E ≃ₐ[F] E) (j : I ≃ J)
    (A : Matrix I I E) (x y : J → E) :
    DualPair.Construction.sesquilinear σ (Matrix.reindex j j A) x y = DualPair.Construction.sesquilinear σ A (x ∘ j) (y ∘ j) := by
  change (fun i => σ (x i)) ⬝ᵥ (A.submatrix j.symm j.symm *ᵥ y) = _
  rw [Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, dotProduct_comp_equiv_symm]
  rfl

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E] {m n : ℕ}
variable (σ : E ≃ₐ[F] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
variable (c : Oscillator.Construction.SymplecticFrame σ H K)

theorem symplecticFrame_continuous [CompleteSpace F] [FiniteDimensional F E]
    (hF : ¬ DiscreteTopology F) (hEmbedding : Continuous (algebraMap F E)) :
    Continuous c.coordinates ∧ Continuous c.coordinates.symm := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField F with hd | ⟨_, rfl⟩
  · exact (hF hd).elim
  · let : ContinuousSMul F E := continuousSMul_of_algebraMap F E hEmbedding
    exact ⟨c.coordinates.toLinearMap.continuous_of_finiteDimensional,
      c.coordinates.symm.toLinearMap.continuous_of_finiteDimensional⟩

def continuousFrameCoordinates [CompleteSpace F] [FiniteDimensional F E]
    (hF : ¬ DiscreteTopology F) (hEmbedding : Continuous (algebraMap F E)) :
    ((Fin m × Fin n) → E) ≃L[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n) where
  toLinearEquiv := c.coordinates
  continuous_toFun := (symplecticFrame_continuous σ H K c hF hEmbedding).1
  continuous_invFun := (symplecticFrame_continuous σ H K c hF hEmbedding).2

def tensorModelCoordinates {J : Type} (j : (Fin m × Fin n) ≃ J)
    (u : (Matrix (Fin m × Fin n) (Fin m × Fin n) E)ˣ)
    (e : ((Fin m × Fin n) → E) ≃L[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n)) :
    (J → E) ≃L[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n) :=
  ((ContinuousLinearEquiv.piCongrLeft F (fun _ : J => E) j).symm.trans
    (MatrixFrameAction.Construction.matrixUnitContinuousLinearEquiv (F := F) u)).trans e

theorem tensorModelCoordinates_apply {J : Type} (j : (Fin m × Fin n) ≃ J)
    (u : (Matrix (Fin m × Fin n) (Fin m × Fin n) E)ˣ)
    (e : ((Fin m × Fin n) → E) ≃L[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n)) (x : J → E) :
    tensorModelCoordinates j u e x = e ((u : Matrix _ _ E) *ᵥ (x ∘ j)) := rfl

theorem tensorModelCoordinates_preserves {J : Type} [Fintype J] [DecidableEq J]
    (j : (Fin m × Fin n) ≃ J)
    (u : (Matrix (Fin m × Fin n) (Fin m × Fin n) E)ˣ)
    (e : ((Fin m × Fin n) → E) ≃L[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n))
    (he : e.toLinearEquiv = c.coordinates) (Q : Matrix J J E)
    (hQ : Matrix.reindex j j (DualPair.Construction.adjointMatrix σ (u : Matrix _ _ E) * (H ⊗ₖ K) * (u : Matrix _ _ E)) = Q)
    (x y : J → E) :
    Oscillator.Construction.standardSymplecticPairing (m * n) (tensorModelCoordinates j u e x) (tensorModelCoordinates j u e y) =
      Algebra.trace F E (DualPair.Construction.sesquilinear σ Q x y) / 2 := by
  rw [tensorModelCoordinates_apply, tensorModelCoordinates_apply]
  change Oscillator.Construction.standardSymplecticPairing (m * n) (e.toLinearEquiv _) (e.toLinearEquiv _) = _
  rw [he, c.preserves]
  unfold DualPair.Construction.traceTensorPairing
  rw [DualPair.Construction.sesquilinear_change, ← sesquilinear_reindex σ j, hQ]

theorem frameSymplectic_injective : Function.Injective (FrameTransport.Construction.frameSymplectic σ H K c) := by
  intro g h hh
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have hv := congrArg (fun t : Oscillator.Construction.TensorSymplectic σ H K => c.coordinates (t.val (c.coordinates.symm v))) hh
  simpa only [FrameTransport.Construction.frameSymplectic_coordinates, c.coordinates.apply_symm_apply] using hv

theorem tensorModelCoordinates_action {J : Type} [Fintype J] [DecidableEq J]
    (j : (Fin m × Fin n) ≃ J)
    (u : (Matrix (Fin m × Fin n) (Fin m × Fin n) E)ˣ)
    (e : ((Fin m × Fin n) → E) ≃L[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n))
    (he : e.toLinearEquiv = c.coordinates) (Q : Matrix J J E)
    (hpair : ∀ x y, Oscillator.Construction.standardSymplecticPairing (m * n) (tensorModelCoordinates j u e x) (tensorModelCoordinates j u e y) =
      Algebra.trace F E (DualPair.Construction.sesquilinear σ Q x y) / 2)
    (g : DualPair.Construction.unitaryGroup σ Q) (t : DualPair.Construction.unitaryGroup σ H × DualPair.Construction.unitaryGroup σ K)
    (hinter : (u : Matrix _ _ E) * (g.val : Matrix J J E).submatrix j j =
      ((DualPair.Construction.tensorUnitaryAction σ H K t).val : Matrix _ _ E) * (u : Matrix _ _ E)) :
    FrameTransport.Construction.frameSymplectic σ H K c (MatrixFrameAction.Construction.matrixFrameAction σ Q (tensorModelCoordinates j u e).toLinearEquiv hpair g) =
      DualPair.Construction.dualPairAction σ H K t := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  apply c.coordinates.injective
  obtain ⟨x, hx⟩ := (tensorModelCoordinates j u e).surjective (c.coordinates v)
  have hxv : (u : Matrix _ _ E) *ᵥ (x ∘ j) = v := by
    apply c.coordinates.injective
    change e.toLinearEquiv ((u : Matrix _ _ E) *ᵥ (x ∘ j)) = _ at hx
    rwa [he] at hx
  rw [FrameTransport.Construction.frameSymplectic_coordinates, ← hx]
  change (MatrixFrameAction.Construction.matrixFrameAction σ Q (tensorModelCoordinates j u e).toLinearEquiv hpair g).val
    ((tensorModelCoordinates j u e).toLinearEquiv x) = _
  rw [MatrixFrameAction.Construction.matrixFrameAction_coordinates]
  change tensorModelCoordinates j u e ((g.val : Matrix J J E) *ᵥ x) = _
  rw [tensorModelCoordinates_apply]
  change e.toLinearEquiv ((u : Matrix _ _ E) *ᵥ (((g.val : Matrix J J E) *ᵥ x) ∘ j)) = _
  rw [he]
  have hp : ((g.val : Matrix J J E) *ᵥ x) ∘ j =
      (g.val : Matrix J J E).submatrix j j *ᵥ (x ∘ j) := by
    rw [Matrix.submatrix_mulVec_equiv]
    simp only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
  rw [hp, Matrix.mulVec_mulVec, hinter, ← Matrix.mulVec_mulVec, hxv]
  rfl

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.TensorFrameCoordinates.Construction
