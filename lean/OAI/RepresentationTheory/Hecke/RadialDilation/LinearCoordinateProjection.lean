import Mathlib

/-! # Linear Coordinate Projection -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.LinearCoordinateProjection.Realization

/-! Evaluate a coordinatewise linear projection without unfolding its coefficient rings. -/

theorem linear_coordinate_projection_apply {R A B I J : Type*} [Semiring R]
    [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
    (P : A →ₗ[R] B) (index : I → J) (x : J → A) (i : I) :
    (LinearMap.pi (fun j => P.comp (LinearMap.proj (index j)))) x i = P (x (index i)) := rfl

end OAI.RepresentationTheory.Hecke.RadialDilation.LinearCoordinateProjection.Realization
