import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.LocalReindexSteps
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.FunctorInverseCoordinates

/-! # Local Reindex Components -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.LocalReindexComponents

noncomputable section

/-! The checked reindexing identities transport the original local
bounded-frame comparison and its equal-open identification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w v' w'
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  {C : Type v} [Category.{w} C] {D : Type v'} [Category.{w'} D]
  (r : D ⥤ C) (O : C ⥤ Y.Opensᵒᵖ)
  (G : C ⥤ (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ)
  (F : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ)
  (ρ : (Functor.const C).obj F ⟶ G)
  [IsIso (LocalMap.restriction f n O G F ρ)]

local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p) (J := J) (δ := δ) f n
local notation "ρ'" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SectionReindex.cone f n r G F ρ

local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.LocalReindexSteps.restriction (B := B) r
attribute [local instance] LocalReindexSteps.pulled_isIso

theorem inverse_component (q : ℕ) (d : D) :
    ((inv (LocalMap.restriction f n (r ⋙ O) (r ⋙ G) F ρ')).f q).app d =
      ((inv (LocalMap.restriction f n O G F ρ)).f q).app (r.obj d) := by
  simp only [Cochain.FunctorInverseCoordinates.inverse,
    LocalReindexSteps.restriction_component f n r O G F ρ q d]

theorem comparison_component (q : ℕ) (d : D) :
    ((LocalMap.map f n (r ⋙ O) (r ⋙ G) F ρ').f q).app d =
      ((LocalMap.map f n O G F ρ).f q).app (r.obj d) := by
  change ((LocalReindexSteps.diagonal f n (r ⋙ O) (r ⋙ G)).f q).app d ≫
      ((inv (LocalMap.restriction f n (r ⋙ O) (r ⋙ G) F ρ')).f q).app d =
    ((LocalReindexSteps.diagonal f n O G).f q).app (r.obj d) ≫
      ((inv (LocalMap.restriction f n O G F ρ)).f q).app (r.obj d)
  rw [inverse_component]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.LocalReindexComponents
