import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalTensorMapDescent

/-! # Map Surjective Generators -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.MapSurjectiveGenerators

noncomputable section

/-! Lifting algebra generators suffices for surjectivity of a natural tensor-product map. -/

open TensorProduct

universe u

theorem tensorMap_surjective_of_generators
    {C D A B : Type u} [CommRing C] [CommRing D] [CommRing A] [CommRing B]
    [Algebra C D] [Algebra C A] [Algebra C B]
    (φ : A →ₐ[C] B) (s : Set B) (hs : Algebra.adjoin C s = ⊤)
    (h : ∀ b ∈ s, ∃ x : D ⊗[C] A,
      Algebra.TensorProduct.map (AlgHom.id D D) φ x = (1 : D) ⊗ₜ[C] b) :
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id D D) φ) := by
  let ψ := Algebra.TensorProduct.map (AlgHom.id D D) φ
  let K : Subalgebra C B := (ψ.range.restrictScalars C).comap
    (Algebra.TensorProduct.includeRight (R := C) (A := D) (B := B))
  have hK : (⊤ : Subalgebra C B) ≤ K := by
    rw [← hs]
    apply Algebra.adjoin_le
    intro b hb
    exact h b hb
  have hb (b : B) : (1 : D) ⊗ₜ[C] b ∈ ψ.range := hK (by trivial)
  intro x
  change x ∈ ψ.range
  induction x using TensorProduct.inductionOn with
  | tmul d b =>
    simpa only [smul_tmul', smul_eq_mul, mul_one] using ψ.range.smul_mem (hb b) d
  | add x y hx hy => exact ψ.range.add_mem hx hy

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.MapSurjectiveGenerators
