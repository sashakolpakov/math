import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Type Geometric Point Lift -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.TypeGeometricPointLift

noncomputable section

/-! Geometric points lift through surjective morphisms locally of
finite type, by taking a closed point of their nonempty geometric fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem exists_geometric_point_lift {S T : Scheme.{u}} (b : T ⟶ S)
    [Surjective b] [LocallyOfFiniteType b]
    {K : Type u} [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S) :
    ∃ t : Spec (.of K) ⟶ T, t ≫ b = s := by
  let Y := pullback b s
  let ρ : Y ⟶ Spec (.of K) := pullback.snd b s
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace ρ
  have : Nonempty Y := ⟨(ρ.surjective (IsLocalRing.closedPoint K)).choose⟩
  obtain ⟨y, _, hy⟩ := nonempty_inter_closedPoints (Set.univ_nonempty : (Set.univ : Set Y).Nonempty)
    isOpen_univ.isLocallyClosed
  let r := pointOfClosedPoint ρ y hy
  have hr : r ≫ ρ = 𝟙 _ := pointOfClosedPoint_comp ρ y hy
  refine ⟨r ≫ pullback.fst b s, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hr, Category.id_comp]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.TypeGeometricPointLift
