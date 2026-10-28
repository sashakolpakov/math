import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactInjective
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.ResolutionMap

/-! # Injective Pullback Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.InjectivePullbackCoordinates.BoundedInjectivePullbackCoordinates

noncomputable section

/-! The exact-functor injective comparison is the original bounded
geometric resolution map used to compute crystalline Ext pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)
  (I : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) fY n))
  (I' : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f n))

theorem map_eq : ExactInjective.ExactInjectivePullback.map
    (IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n)
    (IntegralComparison.BoundedOpen.Sheaves.structureTransport g hg n) I I' =
      IntegralComparison.BoundedGeneral.ResolutionMap.map g hg n I I' := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.InjectivePullbackCoordinates.BoundedInjectivePullbackCoordinates
