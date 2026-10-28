import OAI.RepresentationTheory.Weil.UnitarySplitting.ProductGaussianPhase
import OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyCompositionPhase

/-! # Cayley Matrix Coordinates -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyMatrixCoordinates.Construction

noncomputable section

/-! Transport of the actual Cayley phase into matrix coordinates. -/

open _root_.Matrix

theorem cayleyMatrix_inverse_coordinates
    {F E V : Type} [Field F] [Field E] [Algebra F E]
    [AddCommGroup V] [Module F V] {d : ℕ}
    (e : (Fin d → E) → V) (D : V ≃ₗ[F] V) (A : Matrix (Fin d) (Fin d) E)
    (hA : A.det ≠ 0) (hD : ∀ x, D (e x) = e (A *ᵥ x)) (x : Fin d → E) :
    D.symm (e x) = e (A⁻¹ *ᵥ x) := by
  apply D.injective
  rw [D.apply_symm_apply, hD, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA), Matrix.one_mulVec]

theorem cayleyWeylPhase_matrix_coordinates
    {F E V : Type} [Field F] [Field E] [Algebra F E] [CharZero F]
    [AddCommGroup V] [Module F V] {d : ℕ}
    (σ : E ≃ₐ[F] E) (Q : Matrix (Fin d) (Fin d) E)
    (β : LinearMap.BilinForm F V) (e : (Fin d → E) → V)
    (he : ∀ x y, β (e x) (e y) = Algebra.trace F E (DualPair.Construction.sesquilinear σ Q x y) / 2)
    (D : V ≃ₗ[F] V) (A : Matrix (Fin d) (Fin d) E)
    (hA : A.det ≠ 0) (hD : ∀ x, D (e x) = e (A *ᵥ x)) (x : Fin d → E) :
    CayleyCompositionPhase.Construction.cayleyWeylPhase β D (e x) = Algebra.trace F E (DualPair.Construction.sesquilinear σ Q (A⁻¹ *ᵥ x) x) / 4 := by
  rw [CayleyCompositionPhase.Construction.cayleyWeylPhase, cayleyMatrix_inverse_coordinates e D A hA hD, he]
  ring

theorem cayleyWeylPhase_unitary_sum_coordinates
    {F E V : Type} [Field F] [Field E] [Algebra F E] [CharZero F]
    [AddCommGroup V] [Module F V] {d : ℕ}
    (σ : E ≃ₐ[F] E) (hσ : Function.Involutive σ)
    (Q : Matrix (Fin d) (Fin d) E) (hQ : Q.det ≠ 0) (hskew : DualPair.Construction.adjointMatrix σ Q = -Q)
    (g h : DualPair.Construction.unitaryGroup σ Q) (hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q)
    (hh : h ∈ Generic.Construction.unitaryGenericDomain σ Q) (hgh : g * h ∈ Generic.Construction.unitaryGenericDomain σ Q)
    (β : LinearMap.BilinForm F V) (e : (Fin d → E) → V)
    (he : ∀ x y, β (e x) (e y) = Algebra.trace F E (DualPair.Construction.sesquilinear σ Q x y) / 2)
    (Dg Dh : V ≃ₗ[F] V)
    (hDg : ∀ x, Dg (e x) = e (((g.val : Matrix (Fin d) (Fin d) E) - 1) *ᵥ x))
    (hDh : ∀ x, Dh (e x) = e (((h.val : Matrix (Fin d) (Fin d) E) - 1) *ᵥ x)) (x : Fin d → E) :
    CayleyCompositionPhase.Construction.cayleyWeylPhase β Dg (e x) + CayleyCompositionPhase.Construction.cayleyWeylPhase β Dh (e x) =
      HermitianNormForms.Construction.hermitianTraceQuadratic σ (GaussianDiscriminant.Construction.unitaryProductGaussianMatrix σ Q g h) x := by
  rw [cayleyWeylPhase_matrix_coordinates σ Q β e he Dg _ hg hDg,
    cayleyWeylPhase_matrix_coordinates σ Q β e he Dh _ hh hDh]
  exact (ProductGaussianPhase.Construction.unitaryProductGaussianMatrix_phase σ hσ Q hQ hskew g h hg hh hgh x).symm

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyMatrixCoordinates.Construction
