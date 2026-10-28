import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

/-! # Crystalline Diagram -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Open.CrystallineDiagram

noncomputable section

/-! A diagram of actual open crystalline thickenings retains its
original rings and maps when viewed in the small crystalline site. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
  {C : Type v} [Category.{w} C]
  (F : C ⥤ BigCrystallineSite.Object p B J δ f)
  (hOpen : ∀ c, IsOpenImmersion (F.obj c).mapToX)

def object (c : C) : Crystalline.Site.AffineThickening p B J δ f where
  ring := (F.obj c).ring
  base := (F.obj c).base
  ideal := (F.obj c).ideal
  dividedPowers := (F.obj c).dividedPowers
  baseCompatible := (F.obj c).baseCompatible
  primeNilpotent := (F.obj c).primeNilpotent
  nilIdeal := (F.obj c).nilIdeal
  openMap := (F.obj c).mapToX
  isOpenImmersion := hOpen c
  overBase := (F.obj c).overBase

def map {c d : C} (a : c ⟶ d) : object F hOpen c ⟶ object F hOpen d where
  ringMap := (F.map a).ringMap
  overBase := (F.map a).overBase
  overX := (F.map a).overX

def functor : C ⥤ Crystalline.Site.AffineThickening p B J δ f where
  obj := object F hOpen
  map := CrystallineDiagram.map F hOpen
  map_id c := by
    apply Crystalline.Site.AffineThickening.Hom.ext
    exact congrArg BigCrystallineSite.Object.Hom.ringMap (F.map_id c)
  map_comp a b := by
    apply Crystalline.Site.AffineThickening.Hom.ext
    exact congrArg BigCrystallineSite.Object.Hom.ringMap (F.map_comp a b)

def inclusionIso : functor F hOpen ⋙ BigCrystallineSite.fromSmall ≅ F :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by simp; rfl)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Open.CrystallineDiagram
