import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.ChangeNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

/-! # Frame Complex Functor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor

noncomputable section

/-! Original frame de Rham complexes form a strict contravariant functor
using the actual divided-power form maps of crystalline morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

def functor : (IntegralComparison.BigCrystallineSite.Object p B J δ f)ᵒᵖ ⥤ CochainComplex (ModuleCat.{u} B) ℕ where
  obj F := IntegralComparison.RelativeFrame.ComplexMap.frameComplex F.unop
  map α := IntegralComparison.RelativeFrame.ChangeNaturality.frameMap _ _ α.unop
  map_id F := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact (IntegralComparison.Crystalline.DeRham.formsPresheaf f n).map_id F
  map_comp α β := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact (IntegralComparison.Crystalline.DeRham.formsPresheaf f n).map_comp α β

theorem map_f {F G : (IntegralComparison.BigCrystallineSite.Object p B J δ f)ᵒᵖ} (α : F ⟶ G) (n : ℕ) :
    ((functor f).map α).f n = (IntegralComparison.Crystalline.DeRham.formsPresheaf f n).map α := rfl

def bounded (n : ℕ) : (IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ ⥤ CochainComplex (ModuleCat.{u} B) ℕ :=
  (IntegralComparison.BoundedCrystalline.Site.inclusion f n).op ⋙ functor f

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor
