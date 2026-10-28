import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameComplexFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence

/-! # Frame Postcompose Complex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FramePostcomposeComplex.CrystallineFramePostcomposeComplex

noncomputable section

/-! Geometric postcomposition changes the base map of a frame and
preserves its original divided-power de Rham complex. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = fX) (n : ℕ)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n

def iso : (G).op ⋙ FrameComplexFunctor.CrystallineFrameComplexFunctor.bounded fY n ≅
    FrameComplexFunctor.CrystallineFrameComplexFunctor.bounded fX n :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro U V a
    simp only [Iso.refl_hom]
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FramePostcomposeComplex.CrystallineFramePostcomposeComplex
