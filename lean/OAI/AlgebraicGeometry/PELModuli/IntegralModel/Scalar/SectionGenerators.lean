import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Section Generators -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Scalar.SectionGenerators

noncomputable section

/-! Generators of an original module generate every surjective scalar
extension through the images of their canonical pure tensors. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u

theorem scalar_images_span_of_surjective
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (M : ModuleCat.{u} R) (N : ModuleCat.{u} A)
    (b : (ModuleCat.extendScalars f).obj M ⟶ N) (hb : Function.Surjective b)
    {ι : Type*} (v : ι → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span A (Set.range (fun i => b ((1 : A) ⊗ₜ[R,f] v i))) = ⊤ := by
  let : Algebra R A := f.toAlgebra
  let q := (ModuleCat.extendRestrictScalarsAdj f).homEquiv M N b
  let ψ : M →ₛₗ[f] N :=
    { q.hom.toAddHom with map_smul' := fun r m => q.hom.map_smul r m }
  let Q := Submodule.span A (Set.range (fun i => b ((1 : A) ⊗ₜ[R,f] v i)))
  have hψ (m : M) : ψ m ∈ Q := by
    apply (Submodule.image_span_subset ψ (Set.range v) Q).mpr _ ⟨m, ?_, rfl⟩
    · rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    · rw [hv]
      trivial
  apply top_unique
  intro y hy
  clear hy
  obtain ⟨z, rfl⟩ := hb y
  change b z ∈ Q
  induction z using TensorProduct.inductionOn with
  | tmul a m =>
      let a' : A := a
      let m' : M := m
      change b (a' ⊗ₜ[R] m') ∈ Q
      have he : a' ⊗ₜ[R] m' = a' • ((1 : A) ⊗ₜ[R] m') := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [he, b.hom.map_smul]
      exact Q.smul_mem a' (hψ m')
  | add z w hz hw =>
      rw [map_add]
      exact Q.add_mem hz hw

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Scalar.SectionGenerators
