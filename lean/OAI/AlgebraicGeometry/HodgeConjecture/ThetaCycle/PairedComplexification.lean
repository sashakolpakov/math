import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicTensorComplexCoordinates

/-! # Paired Complexification -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PairedComplexification.CM

noncomputable section

/-! Complex-linear maps of paired CM components are determined by
the actual conjugate pairs coming from the real tensor space. -/

open scoped Classical

theorem paired_complex_linear_ext {I J V : Type} [AddCommMonoid V] [Module ℂ V]
    (f g : (I → ((J → ℂ) × (J → ℂ))) →ₗ[ℂ] V)
    (h : ∀ x : I → J → ℂ, f (fun i => (x i, fun j => star (x i j))) =
      g (fun i => (x i, fun j => star (x i j)))) : f = g := by
  apply LinearMap.ext
  intro w
  let x : I → J → ℂ := fun i j => ((w i).1 j + star ((w i).2 j)) / 2
  let y : I → J → ℂ := fun i j => (-Complex.I / 2) * ((w i).1 j - star ((w i).2 j))
  have he : w = (fun i => (x i, fun j => star (x i j))) +
      Complex.I • (fun i => (y i, fun j => star (y i j))) := by
    funext i
    apply Prod.ext <;> funext j <;> simp [x, y] <;> ring_nf <;> simp <;> ring
  rw [he, map_add, map_smul, map_add, map_smul, h x, h y]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PairedComplexification.CM
