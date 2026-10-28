import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.EtaleSections

/-! # Etale Algebra Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.EtaleAlgebraMap

noncomputable section

/-! Maps of actual étale affine factors act on their canonical crystalline lifts and sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.EtaleResidue OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.EtaleLift

attribute [local instance] EtaleResidue.objectAlgebra

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
  (A C : Type u) [CommRing A] [CommRing C] [Algebra B A] [Algebra B C]
  (ψ : A →ₐ[B] C) (j : X ⟶ Spec (CommRingCat.of A)) (g : X ⟶ Spec (CommRingCat.of C))
  (hrel : j = g ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom))

include hrel in
theorem residue (U : BigCrystallineSite.Object p B J δ f) :
    EtaleResidue.residueRingMap A j U = (EtaleResidue.residueRingMap C g U).comp ψ.toRingHom := by
  have h : Spec.preimage (U.mapToX ≫ j) =
      CommRingCat.ofHom ψ.toRingHom ≫ Spec.preimage (U.mapToX ≫ g) := by
    rw [hrel, ← Category.assoc, Spec.preimage_comp, Spec.preimage_map]
  exact congrArg CommRingCat.Hom.hom h

variable [Algebra.Etale B A] [Algebra.Etale B C]
  (hj : j ≫ Spec.map (CommRingCat.ofHom (algebraMap B A)) = f)
  (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) = f)

include hrel in
theorem lift_comp (U : BigCrystallineSite.Object p B J δ f) :
    EtaleLift.lift A j hj U = (EtaleLift.lift C g hg U).comp ψ := by
  symm
  apply EtaleLift.unique A j hj U
  apply AlgHom.ext
  intro a
  change Ideal.Quotient.mk U.ideal (EtaleLift.lift C g hg U (ψ a)) = EtaleResidue.residueRingMap A j U a
  exact (EtaleLift.reduction_apply C g hg U (ψ a)).trans (RingHom.congr_fun (residue A C ψ j g hrel U) a).symm

include hrel in
theorem section_comp (a : A) :
    EtaleSections.sectionOf (p := p) (J := J) (δ := δ) A j hj a =
      EtaleSections.sectionOf C g hg (ψ a) := by
  apply ConstantSections.ext f
  intro U
  rw [EtaleSections.value_sectionOf, EtaleSections.value_sectionOf]
  exact AlgHom.congr_fun (lift_comp A C ψ j g hrel hj hg U) a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.EtaleAlgebraMap
