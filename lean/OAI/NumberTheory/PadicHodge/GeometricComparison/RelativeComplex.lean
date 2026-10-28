import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ComplexRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramComplexMap

/-! # Relative Complex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.RelativeComplex.RelativeComplexRestrictionNaturality

noncomputable section

/-! Restricting the original relative crystalline complex is natural in
maps of its actual diagrams over the fixed base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
universe u v w v' w'
variable {C : Type v} [Category.{w} C] {D : Type v'} [Category.{w'} D]
  {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} (t : D ⥤ C)
  (H K Q : C ⥤ IntegralComparison.BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q) (ρ : K ⟶ Q)
  (θ : H ⟶ K) (hθ : θ ≫ ρ = π)

include hθ in
theorem projection : Functor.whiskerLeft t θ ≫ Functor.whiskerLeft t ρ = Functor.whiskerLeft t π :=
  (Functor.whiskerLeft_comp t θ ρ).symm.trans (congrArg (Functor.whiskerLeft t) hθ)

theorem natural :
    ((IntegralComparison.Relative.ComplexRestriction.restriction (B := B) t).mapHomologicalComplex (.up ℕ)).map
      (IntegralComparison.Relative.DiagramComplexMap.map H K Q π ρ θ hθ) ≫
        (IntegralComparison.Relative.ComplexRestriction.complexIso t H Q π).hom =
    (IntegralComparison.Relative.ComplexRestriction.complexIso t K Q ρ).hom ≫
      IntegralComparison.Relative.DiagramComplexMap.map (t ⋙ H) (t ⋙ K) (t ⋙ Q)
        (Functor.whiskerLeft t π) (Functor.whiskerLeft t ρ) (Functor.whiskerLeft t θ)
        (projection t H K Q π ρ θ hθ) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.RelativeComplex.RelativeComplexRestrictionNaturality
