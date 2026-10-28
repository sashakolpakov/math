import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineDiagramAssembly
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConcreteAffineImmersionModels

/-! # Affine Diagram Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineDiagramDescent

noncomputable section

/-! Every finite diagram of smooth affine algebras with open-immersion arrows has a smooth noetherian model. -/

open TensorProduct _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

theorem exists_smoothAffineDiagramModel_above
    (R : Type u) [CommRing R] {I : Type v} [Finite I] (A : I → Type u)
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, Algebra.Smooth R (A i)]
    {J : Type w} [Finite J] (s t : J → I) (φ : ∀ j, A (s j) →ₐ[R] A (t j))
    [∀ j, IsOpenImmersion (Spec.map (CommRingCat.ofHom (φ j).toRingHom))]
    (C : Subalgebra ℤ R) [Algebra.FiniteType ℤ C] :
    ∃ M : AffineDiagramModel.SmoothAffineDiagramModel R A s t φ, C ≤ M.coefficients := by
  obtain ⟨C₀, hCC, hC, _, B, hB, he⟩ := Common.SmoothAlgebraModels.exists_common_smooth_algebra_models R A C
  have : Algebra.FiniteType ℤ C₀ := hC
  have (i : I) : Algebra.Smooth C₀ (B i) := hB i
  let e (i : I) : A i ≃ₐ[R] R ⊗[C₀] B i := (he i).some
  let p (j : J) : R ⊗[C₀] B (s j) →ₐ[R] R ⊗[C₀] B (t j) :=
    Affine.ModelConjugation.modelConjugateMap (e (s j)) (e (t j)) (φ j)
  have (j : J) : IsOpenImmersion (Spec.map (CommRingCat.ofHom (p j).toRingHom)) :=
    Affine.ModelConjugation.modelConjugateMap_isOpenImmersion (e (s j)) (e (t j)) (φ j)
  obtain ⟨D, _, hD, ψ, hψ, F, hF, hImm⟩ := ConcreteAffineImmersionModels.exists_common_flat_openImmersion_models
    (C := C₀) (R := R) (fun j => ↥(B (s j))) (fun j => ↥(B (t j)))
    p (⊥ : Subalgebra C₀ R) Subalgebra.fg_bot
  have hImm' (j : J) : IsOpenImmersion (Spec.map
      (CommRingCat.ofHom (Iterated.AffineModelRecovery.iteratedCoefficientArrow D F (ψ j)).toRingHom)) := hImm j
  obtain ⟨M, hM⟩ := AffineDiagramAssembly.exists_smoothAffineDiagramModel_from_coefficients
    A s t φ C₀ B e D F hD hF ψ hψ hImm'
  exact ⟨M, hCC.trans hM⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineDiagramDescent
