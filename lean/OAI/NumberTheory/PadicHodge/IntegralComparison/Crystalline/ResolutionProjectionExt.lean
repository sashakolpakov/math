import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ResolutionProjectionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedResolutionLevels

/-! # Resolution Projection Ext -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionProjectionExt

noncomputable section

/-! The projections of the reconstructed original resolution induce exactly the original bounded crystalline restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "I" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedResolution.Comparison.resolution (p := p) (J := J) (δ := δ) f
local notation "r" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedResolutionLevels.projection (p := p) (J := J) (δ := δ) f n

theorem projection_eq : Bounded.ResolutionProjectionBase.Coordinates.projection f n I = r := by
  apply HomologicalComplex.Hom.ext
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem homology (i : ℕ) : HomologicalComplex.homologyMap r i ≫
    (BoundedResolutionLevels.homologyIso f n i).hom =
      (BoundedResolution.Comparison.homologyIso f i).hom ≫
        ModuleCat.ofHom (BoundedCrystalline.CrystallineCohomology.restriction f n i) :=
  (congrArg (fun b => HomologicalComplex.homologyMap b i ≫
    (BoundedResolutionLevels.homologyIso f n i).hom) (projection_eq f n).symm).trans
      (Bounded.ResolutionProjectionCoordinates.homology f n I i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionProjectionExt
