import OAI.RepresentationTheory.Theta.Geometric.PointCotangent

/-! # Cotangent Value Ext -/

namespace OAI.RepresentationTheory.Theta.Geometric.CotangentValueExt

noncomputable section

/-! The differential generators detect complex-linear maps from an
actual cotangent fiber, with no coefficient-ring action supplied. -/

open scoped TensorProduct

theorem pointCotangent_complexLinearMap_ext {A M : Type} [CommRing A]
    [Algebra ℂ A] [Algebra A ℂ] [IsScalarTower ℂ A ℂ]
    [AddCommGroup M] [Module ℂ M]
    (f g : PointCotangent.pointCotangent ℂ A →ₗ[ℂ] M)
    (h : ∀ a : A, f (1 ⊗ₜ[A] KaehlerDifferential.D ℂ A a) =
      g (1 ⊗ₜ[A] KaehlerDifferential.D ℂ A a)) : f = g := by
  let : Module A M := Module.compHom M (algebraMap A ℂ)
  let : IsScalarTower A ℂ M := IsScalarTower.of_compHom _ _ _
  let : IsScalarTower ℂ A M := by
    constructor
    intro c a v
    change algebraMap A ℂ (c • a) • v = c • (algebraMap A ℂ a • v)
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, mul_smul]
  exact PointCotangent.pointCotangent_linearMap_ext ℂ A f g h

end

end OAI.RepresentationTheory.Theta.Geometric.CotangentValueExt
