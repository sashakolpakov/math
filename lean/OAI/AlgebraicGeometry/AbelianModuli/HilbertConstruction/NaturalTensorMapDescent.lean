import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatTensorIsoDescent

/-! # Natural Tensor Map Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalTensorMapDescent

noncomputable section

/-! Isomorphism descent for the natural base change of a fixed algebra map. -/

open TensorProduct

universe u v

variable {C R A B : Type u} [CommRing C] [CommRing R] [CommRing A] [CommRing B]
variable [Algebra C R] [Algebra C A] [Algebra C B]

theorem coefficientTensorMap_natural (D : Subalgebra C R) (φ : A →ₐ[C] B) (x : D ⊗[C] A) :
    Coefficient.TensorMaps.coefficientTensorMap D (Algebra.TensorProduct.map (AlgHom.id D D) φ x) =
      Algebra.TensorProduct.map (AlgHom.id R R) φ (Coefficient.TensorMaps.coefficientTensorMap D x) := by
  induction x using TensorProduct.inductionOn with
  | tmul d a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem exists_common_natural_tensorMap_bijective {ι : Type v} [Finite ι]
    (A B : ι → Type u) [∀ i, CommRing (A i)] [∀ i, CommRing (B i)]
    [∀ i, Algebra C (A i)] [∀ i, Algebra C (B i)]
    [∀ i, Algebra.FiniteType C (A i)] [∀ i, Algebra.FiniteType C (B i)]
    [∀ i, Module.Flat C (A i)] [∀ i, Module.Flat C (B i)]
    (φ : ∀ i, A i →ₐ[C] B i)
    (hφ : ∀ i, Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R R) (φ i)))
    (E : Subalgebra C R) (hE : E.FG) :
    ∃ D : Subalgebra C R, E ≤ D ∧ D.FG ∧
      ∀ i, Function.Bijective (Algebra.TensorProduct.map (AlgHom.id D D) (φ i)) := by
  let e (i : ι) : R ⊗[C] A i ≃ₐ[R] R ⊗[C] B i :=
    AlgEquiv.ofBijective (Algebra.TensorProduct.map (AlgHom.id R R) (φ i)) (hφ i)
  obtain ⟨D, hED, hD, hd⟩ := HilbertConstruction.Finite.FlatTensorIsoDescent.exists_common_flat_tensorIso_descent A B e E hE
  refine ⟨D, hED, hD, ?_⟩
  intro i
  obtain ⟨eD, heD, _⟩ := hd i
  have heq : eD.toAlgHom = Algebra.TensorProduct.map (AlgHom.id D D) (φ i) := by
    apply AlgHom.ext
    intro x
    apply Coefficient.TensorMaps.coefficientTensorMap_injective D
    exact (heD.1 x).trans (coefficientTensorMap_natural D (φ i) x).symm
  exact (congrArg (fun f : D ⊗[C] A i →ₐ[D] D ⊗[C] B i => Function.Bijective f) heq).mp
    eD.bijective

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalTensorMapDescent
