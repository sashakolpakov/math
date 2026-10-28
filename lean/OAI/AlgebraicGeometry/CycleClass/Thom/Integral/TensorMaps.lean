import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Tensor Maps -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Integral.TensorMaps.Constructions

noncomputable section

/-! The tensor product of actual integral algebra homomorphisms is integral. -/

open scoped TensorProduct

variable {k P Q A B : Type*} [CommRing k]
  [CommRing P] [CommRing Q] [CommRing A] [CommRing B]
  [Algebra k P] [Algebra k Q] [Algebra k A] [Algebra k B]

theorem tensorMap_isIntegral (f : P →ₐ[k] A) (g : Q →ₐ[k] B)
    (hf : f.IsIntegral) (hg : g.IsIntegral) : (Algebra.TensorProduct.map f g).IsIntegral := by
  let : Algebra P A := f.toRingHom.toAlgebra
  let : Algebra Q B := g.toRingHom.toAlgebra
  let : Algebra (P ⊗[k] Q) (A ⊗[k] B) := (Algebra.TensorProduct.map f g).toRingHom.toAlgebra
  have hA (a : A) : IsIntegral (P ⊗[k] Q) (a ⊗ₜ[k] (1 : B)) := by
    apply IsIntegral.map_of_comp_eq
      (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] Q).toRingHom
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toRingHom
      (a := a) _ (hf a)
    ext r
    change (Algebra.TensorProduct.map f g) (r ⊗ₜ[k] (1 : Q)) = f r ⊗ₜ[k] (1 : B)
    simp
  have hB (b : B) : IsIntegral (P ⊗[k] Q) ((1 : A) ⊗ₜ[k] b) := by
    apply IsIntegral.map_of_comp_eq
      (Algebra.TensorProduct.includeRight : Q →ₐ[k] P ⊗[k] Q).toRingHom
      (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom
      (a := b) _ (hg b)
    ext r
    change (Algebra.TensorProduct.map f g) ((1 : P) ⊗ₜ[k] r) = (1 : A) ⊗ₜ[k] g r
    simp
  intro x
  change IsIntegral (P ⊗[k] Q) x
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
      simpa only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] using (hA a).mul (hB b)
  | add x y hx hy => exact hx.add hy

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Integral.TensorMaps.Constructions
