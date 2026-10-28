import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameComplexFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryDeRhamFunctor

/-! # Frame Ring Functor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameRingFunctor.CrystallineFrameRingFunctor

noncomputable section

/-! Ambient rings of actual crystalline objects form a contravariant
algebra-valued functor with the original ambient ring maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

local instance objectAlgebra (F : IntegralComparison.BigCrystallineSite.Object p B J δ f) : Algebra B F.ring := F.base.toAlgebra

def functor : (IntegralComparison.BigCrystallineSite.Object p B J δ f)ᵒᵖ ⥤ CommAlgCat.{u} B where
  obj F := CommAlgCat.of B F.unop.ring
  map α := CommAlgCat.ofHom (IntegralComparison.Crystalline.DeRham.ambientMap f α.unop)
  map_id F := by ext x; rfl
  map_comp α β := by ext x; rfl

def bounded (n : ℕ) : (IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ ⥤ CommAlgCat.{u} B :=
  (IntegralComparison.BoundedCrystalline.Site.inclusion f n).op ⋙ functor f

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameRingFunctor.CrystallineFrameRingFunctor
