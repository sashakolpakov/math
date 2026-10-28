import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FramePostcomposition

/-! # Postcomposition -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.Postcomposition.CrystallineFrameGeometricPostcomposition

noncomputable section

/-! A compatible map of affine charts induces a map of the original
global crystalline frames over an arbitrary geometric morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {U V X Y : Scheme.{u}} {fU : U ⟶ Spec (CommRingCat.of B)}
  {fV : V ⟶ Spec (CommRingCat.of B)} {fX : X ⟶ Spec (CommRingCat.of B)}
  {fY : Y ⟶ Spec (CommRingCat.of B)}
  (s : U ⟶ V) (g : X ⟶ Y) (jU : U ⟶ X) (jV : V ⟶ Y)
  (hs : s ≫ fV = fU) (hg : g ≫ fY = fX)
  (hjU : jU ≫ fX = fU) (hjV : jV ≫ fY = fV)
  (h : s ≫ jV = jU ≫ g) (n : ℕ)
  {FU : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fU n}
  {FV : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fV n}
  (a : (IntegralComparison.BoundedOpen.Equivalence.postcompose s hs n).obj FU ⟶ FV)

def map : (IntegralComparison.BoundedOpen.Equivalence.postcompose g hg n).obj
    ((IntegralComparison.BoundedOpen.Equivalence.postcompose jU hjU n).obj FU) ⟶
      (IntegralComparison.BoundedOpen.Equivalence.postcompose jV hjV n).obj FV :=
  ((IntegralComparison.Crystalline.PostcomposeComposition.boundedIso jU g hjU hg n).app FU).hom ≫
    FramePostcomposition.CrystallineFramePostcomposition.map s jV (jU ≫ g) hs hjV
      (IntegralComparison.Crystalline.PostcomposeComposition.overBase jU g hjU hg) h n a

theorem ringMap : (map s g jU jV hs hg hjU hjV h n a).hom.ringMap = a.hom.ringMap := by
  ext x
  exact congrArg (fun q => q x) (FramePostcomposition.CrystallineFramePostcomposition.ringMap s jV (jU ≫ g)
    hs hjV (IntegralComparison.Crystalline.PostcomposeComposition.overBase jU g hjU hg) h n a)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.Postcomposition.CrystallineFrameGeometricPostcomposition
