import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ComplexRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ResolutionFunctor

/-! # Relative Restriction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.RelativeRestriction.RelativeRestrictionMap

noncomputable section

/-! Restricting the actual relative diagram map commutes with the original
relative-complex restriction isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
universe u v w v' w'
variable {C : Type v} [Category.{w} C] {D : Type v'} [Category.{w'} D]
  {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} (t : D ⥤ C)
  (H K Q : C ⥤ IntegralComparison.BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q) (ρ : K ⟶ Q)
  (θ : H ⟶ K) (hθ : θ ≫ ρ = π)

include hθ in
theorem projection : Functor.whiskerLeft t θ ≫ Functor.whiskerLeft t ρ = Functor.whiskerLeft t π := by
  rw [← Functor.whiskerLeft_comp, hθ]

def map := IntegralComparison.Relative.DiagramComplexMap.map (t ⋙ H) (t ⋙ K) (t ⋙ Q)
  (Functor.whiskerLeft t π) (Functor.whiskerLeft t ρ) (Functor.whiskerLeft t θ)
    (projection t H K Q π ρ θ hθ)

theorem square :
    ((IntegralComparison.Relative.ComplexRestriction.restriction (B := B) t).mapHomologicalComplex (.up ℕ)).map
      (IntegralComparison.Relative.DiagramComplexMap.map H K Q π ρ θ hθ) ≫
        (IntegralComparison.Relative.ComplexRestriction.complexIso t H Q π).hom =
    (IntegralComparison.Relative.ComplexRestriction.complexIso t K Q ρ).hom ≫ RelativeRestrictionMap.map t H K Q π ρ θ hθ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  rfl

theorem restrictedMap_isIso [IsIso (Functor.whiskerLeft t θ)] :
    IsIso (RelativeRestrictionMap.map t H K Q π ρ θ hθ) := by
  exact (IntegralComparison.Relative.ResolutionFunctor.diagramIso (t ⋙ Q)
    (Functor.whiskerLeft t π) (Functor.whiskerLeft t ρ) (asIso (Functor.whiskerLeft t θ))
      (projection t H K Q π ρ θ hθ)).isIso_hom

theorem isIso [IsIso (Functor.whiskerLeft t θ)] :
    IsIso (((IntegralComparison.Relative.ComplexRestriction.restriction (B := B) t).mapHomologicalComplex (.up ℕ)).map
      (IntegralComparison.Relative.DiagramComplexMap.map H K Q π ρ θ hθ)) := by
  let := restrictedMap_isIso t H K Q π ρ θ hθ
  have h : IsIso
      (((IntegralComparison.Relative.ComplexRestriction.restriction (B := B) t).mapHomologicalComplex (.up ℕ)).map
        (IntegralComparison.Relative.DiagramComplexMap.map H K Q π ρ θ hθ) ≫
          (IntegralComparison.Relative.ComplexRestriction.complexIso t H Q π).hom) := by
    rw [square]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (IntegralComparison.Relative.ComplexRestriction.complexIso t H Q π).hom

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.RelativeRestriction.RelativeRestrictionMap
