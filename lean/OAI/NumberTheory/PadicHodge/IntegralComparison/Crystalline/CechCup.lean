import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.Cup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.CrystallineSeparatedProduct

/-! # Cech Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CechCup

noncomputable section

/-! Alexander–Whitney multiplication on Čech cochains of the original
crystalline structure coefficient. The ring lift is exactly the universe
lift already used by the additive crystalline structure presheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f]

local instance : HasBinaryProducts (Site.AffineThickening p B J δ f) :=
  Small.CrystallineSeparatedProduct.hasBinaryProducts f (Fact.out : p.Prime).pos

def structureRingPresheaf : (Site.AffineThickening p B J δ f)ᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj U := CommRingCat.of (ULift.{u + 1} U.unop.ring)
  map α := CommRingCat.ofHom
    { toFun := fun x => ⟨α.unop.ringMap x.down⟩
      map_one' := by ext; exact map_one α.unop.ringMap.toRingHom
      map_mul' := fun x y => by ext; exact map_mul α.unop.ringMap.toRingHom x.down y.down
      map_zero' := by ext; exact map_zero α.unop.ringMap.toRingHom
      map_add' := fun x y => by ext; exact map_add α.unop.ringMap.toRingHom x.down y.down }
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

def structureForgetIso : structureRingPresheaf (p := p) (J := J) (δ := δ) f ⋙
    Cech.Cup.forgetRing ≅
      Site.AffineThickening.structureAbPresheaf (p := p) (B := B) (J := J) (δB := δ) (f := f) :=
  Iso.refl _

variable {ι : Type (u + 1)} (U : ι → Site.AffineThickening p B J δ f)

def complex : CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  (NonemptyCechNerve.complexFunctor U).obj
    (Site.AffineThickening.structureAbPresheaf (p := p) (B := B) (J := J) (δB := δ) (f := f))

def originalIso : Cech.Cup.nativeComplex U (structureRingPresheaf f) ≅ complex f U :=
  (NonemptyCechNerve.complexFunctor U).mapIso (structureForgetIso f)

def cup {m n : ℕ} (x : (complex f U).X m) (y : (complex f U).X n) :
    (complex f U).X (m + n) :=
  (originalIso f U).hom.f (m + n)
    (Cech.Cup.cup U (structureRingPresheaf f)
      ((originalIso f U).inv.f m x) ((originalIso f U).inv.f n y))

theorem cup_isCocycle {m n : ℕ} (x : (complex f U).X m) (y : (complex f U).X n)
    (hx : (complex f U).d m (m + 1) x = 0)
    (hy : (complex f U).d n (n + 1) y = 0) :
    (complex f U).d (m + n) (m + n + 1) (cup f U x y) = 0 := by
  have hxm : (Cech.Cup.nativeComplex U (structureRingPresheaf f)).d m (m + 1)
      ((originalIso f U).inv.f m x) = 0 := by
    exact (ConcreteCategory.congr_hom ((originalIso f U).inv.comm m (m + 1)) x).trans
      ((congrArg ((originalIso f U).inv.f (m + 1)) hx).trans (map_zero _))
  have hyn : (Cech.Cup.nativeComplex U (structureRingPresheaf f)).d n (n + 1)
      ((originalIso f U).inv.f n y) = 0 := by
    exact (ConcreteCategory.congr_hom ((originalIso f U).inv.comm n (n + 1)) y).trans
      ((congrArg ((originalIso f U).inv.f (n + 1)) hy).trans (map_zero _))
  have hz := Cech.Cup.cup_isCocycle U (structureRingPresheaf f) _ _ hxm hyn
  exact (ConcreteCategory.congr_hom ((originalIso f U).hom.comm (m + n) (m + n + 1)) _).trans
    ((congrArg ((originalIso f U).hom.f (m + n + 1)) hz).trans (map_zero _))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CechCup
