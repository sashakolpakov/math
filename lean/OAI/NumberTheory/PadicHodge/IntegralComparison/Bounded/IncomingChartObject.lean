import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence

/-! # Incoming Chart Object -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.IncomingChartObject

noncomputable section

/-! A native bounded object mapping to a chart frame is an actual
postcomposition of a bounded object over that chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  (V : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n)
  (α : V ⟶ (BoundedOpen.Equivalence.postcompose g hg n).obj F)

include α in
theorem factorization : Crystalline.OpenCondition.property g V.obj :=
  Crystalline.OpenCondition.incoming g α.hom ⟨F.obj.mapToX, rfl⟩

def object : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n :=
  ⟨Crystalline.OpenCondition.liftObject g hg V.obj
    (factorization g hg n F V α).choose (factorization g hg n F V α).choose_spec, V.property⟩

def iso : (BoundedOpen.Equivalence.postcompose g hg n).obj (object g hg n F V α) ≅ V :=
  (BoundedCrystalline.Site.property fY n).isoMk
    (Crystalline.OpenCondition.liftIso g hg V.obj
      (factorization g hg n F V α).choose (factorization g hg n F V α).choose_spec)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.IncomingChartObject
