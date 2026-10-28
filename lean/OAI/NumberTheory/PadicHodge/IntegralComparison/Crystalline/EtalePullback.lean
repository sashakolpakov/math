import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.EtaleSections

/-! # Etale Pullback -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.EtalePullback

noncomputable section

/-! The canonical étale lifts and actual crystalline sections respect pullback of the original scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.EtaleResidue OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.EtaleLift

attribute [local instance] EtaleResidue.objectAlgebra

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (A : Type u) [CommRing A] [Algebra B A]
  (g : Y ⟶ Spec (CommRingCat.of A))
  (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap B A)) = fY)
  (h : X ⟶ Y) (hh : h ≫ fY = fX)

include hg hh in
theorem overBase : (h ≫ g) ≫ Spec.map (CommRingCat.ofHom (algebraMap B A)) = fX := by
  rw [Category.assoc, hg, hh]

theorem residue (U : BigCrystallineSite.Object p B J δ fX) :
    EtaleResidue.residueMap A g hg ((BigCrystallineSite.postcompose h hh).obj U) = EtaleResidue.residueMap A (h ≫ g) (overBase A g hg h hh) U := by
  apply AlgHom.ext
  intro a
  exact ConcreteCategory.congr_hom (congrArg Spec.preimage (Category.assoc U.mapToX h g)) a

variable [Algebra.Etale B A]

theorem lift_pullback (U : BigCrystallineSite.Object p B J δ fX) :
    EtaleLift.lift A g hg ((BigCrystallineSite.postcompose h hh).obj U) = EtaleLift.lift A (h ≫ g) (overBase A g hg h hh) U := by
  apply EtaleLift.unique A (h ≫ g) (overBase A g hg h hh) U
  exact (EtaleLift.reduction A g hg ((BigCrystallineSite.postcompose h hh).obj U)).trans (residue A g hg h hh U)

theorem section_pullback (a : A) :
    Functor.whiskerLeft (BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) h hh).op
        (EtaleSections.sectionOf A g hg a) ≫
      (BigCrystallineCohomology.presheafTransport h hh).hom =
        EtaleSections.sectionOf A (h ≫ g) (overBase A g hg h hh) a := by
  apply ConstantSections.ext fX
  intro U
  change ConstantSections.value fY (EtaleSections.sectionOf A g hg a)
      ((BigCrystallineSite.postcompose h hh).obj U) =
    ConstantSections.value fX
      (EtaleSections.sectionOf A (h ≫ g) (overBase A g hg h hh) a) U
  rw [EtaleSections.value_sectionOf, EtaleSections.value_sectionOf]
  exact AlgHom.congr_fun (lift_pullback A g hg h hh U) a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.EtalePullback
