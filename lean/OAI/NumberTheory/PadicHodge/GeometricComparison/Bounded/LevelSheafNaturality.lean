import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LevelPresheafNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameSheaves

/-! # Level Sheaf Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LevelSheafNaturality.BoundedLevelSheafNaturality

noncomputable section

/-! Exact bounded-level restriction identifies the original relative frame
sheaf resolutions naturally in the frame. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f]
  (n m : ℕ) (hnm : n ≤ m)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p) (J := J) (δ := δ) f n m hnm
local notation "Sn" => Functor.mapHomologicalComplex
  (IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := J) (δ := δ) f n) (ComplexShape.up ℕ)

theorem natural {F F' : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n} (α : F ⟶ F') :
    ((T).mapHomologicalComplex (.up ℕ)).map (IntegralComparison.BoundedFrame.Change.sheafMap ((G).map α)) ≫
      (IntegralComparison.BoundedLevel.FrameSheaves.complexIso f n m hnm F).hom =
    (IntegralComparison.BoundedLevel.FrameSheaves.complexIso f n m hnm F').hom ≫
      IntegralComparison.BoundedFrame.Change.sheafMap α := by
  have h₁ := (NatIso.mapHomologicalComplex
    (IntegralComparison.BoundedLevel.FrameSheaves.sheafificationIso f n m hnm) (.up ℕ)).hom.naturality
      (IntegralComparison.BoundedFrame.Change.presheafMap ((G).map α))
  have h₂ := congrArg (Sn).map (LevelPresheafNaturality.BoundedLevelPresheafNaturality.natural f n m hnm α)
  simp only [Functor.map_comp] at h₂
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

def iso : (G).op ⋙ BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor f m ⋙
    (T).mapHomologicalComplex (.up ℕ) ≅ BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor f n :=
  NatIso.ofComponents (fun F => IntegralComparison.BoundedLevel.FrameSheaves.complexIso f n m hnm F.unop)
    (fun α => natural f n m hnm α.unop)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LevelSheafNaturality.BoundedLevelSheafNaturality
