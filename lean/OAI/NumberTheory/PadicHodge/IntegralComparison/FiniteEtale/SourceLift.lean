import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.SourceLiftReduction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.FiniteReduction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.SourcePointLift

/-! # Source Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SourceLift

noncomputable section

/-! Finite etale lifting across a nilpotent closed target reduction,
with the exact original source fiber. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X₀ X Y₀ : Scheme.{u}} (i : X₀ ⟶ X) [IsClosedImmersion i]
  (hi : IsNilpotent i.ker) (f : Y₀ ⟶ X₀) [Etale f] [IsFinite f]

instance map_finite : IsFinite (IntegralComparison.Etale.SourceLift.map i hi f) := by
  let : Surjective (IntegralComparison.Etale.SourceLift.reduction i hi f) := ⟨IntegralComparison.Etale.SourceLift.reduction_surjective i hi f⟩
  exact IntegralComparison.Etale.FiniteReduction.finite i (IntegralComparison.Etale.SourceLift.reduction i hi f) f (IntegralComparison.Etale.SourceLift.map i hi f) (IntegralComparison.Etale.SourceLift.reduction_map i hi f)

include hi in
theorem exists_finite_etale_lift :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X) (j : Y₀ ⟶ Y),
      IsFinite g ∧ Etale g ∧ IsClosedImmersion j ∧ Surjective j ∧
        CategoryTheory.IsPullback j f g i :=
  ⟨IntegralComparison.Etale.SourceLift.source i hi f, IntegralComparison.Etale.SourceLift.map i hi f, IntegralComparison.Etale.SourceLift.reduction i hi f, inferInstance, inferInstance,
    inferInstance, ⟨IntegralComparison.Etale.SourceLift.reduction_surjective i hi f⟩, IntegralComparison.Etale.SourceLiftReduction.reduction_square i hi f⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SourceLift
