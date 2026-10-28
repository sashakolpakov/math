import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.SheafSectionNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.GeometricMap

/-! # Functor Isomorphisms -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.FunctorIsomorphisms.FrameFunctorIsomorphisms

noncomputable section

/-! Actual isomorphisms of bounded frames induce isomorphisms of
their de Rham complexes, sheaf resolutions and geometric comparison maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (n : ℕ)

omit [Fact p.Prime] [IsSeparated f] in
theorem frameMap {F G : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n} (α : G ⟶ F) [IsIso α] :
    IsIso (IntegralComparison.BoundedFrame.SectionChange.frameMap α) :=
  inferInstanceAs (IsIso ((SheafSectionNaturality.FrameSheafSectionNaturality.source f n).map α.op))

theorem sheafMap {F G : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n} (α : G ⟶ F) [IsIso α] :
    IsIso (IntegralComparison.BoundedFrame.Change.sheafMap α) :=
  inferInstanceAs (IsIso ((BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor f n).map α.op))

variable (g : X ⟶ Y) [Mono g] (hg : g ≫ fY = f)
  {FX : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n}
  {FY : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n}
  (α : (IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).obj FX ⟶ FY)
  [IsIso α]

theorem geometricMap : IsIso (IntegralComparison.BoundedFrame.GeometricMap.map g hg n α) := by
  let := sheafMap n α
  dsimp only [IntegralComparison.BoundedFrame.GeometricMap.map]
  infer_instance

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.FunctorIsomorphisms.FrameFunctorIsomorphisms
