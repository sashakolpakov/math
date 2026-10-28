import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.EtaleResidue

/-! # Etale Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.EtaleLift

noncomputable section

/-! Unique lifts of an actual étale affine factor to every original crystalline thickening. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.EtaleResidue

attribute [local instance] EtaleResidue.objectAlgebra

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
  (A : Type u) [CommRing A] [Algebra B A] [Algebra.Etale B A]
  (g : X ⟶ Spec (CommRingCat.of A))
  (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap B A)) = f)

theorem existsUnique_lift (U : BigCrystallineSite.Object p B J δ f) :
    ∃! l : A →ₐ[B] U.ring, (Ideal.Quotient.mkₐ B U.ideal).comp l = EtaleResidue.residueMap A g hg U :=
  IntegralComparison.Etale.NilLifting.existsUnique_lift (EtaleResidue.residueMap A g hg U) (Ideal.Quotient.mkₐ B U.ideal)
    Ideal.Quotient.mk_surjective (fun x hx => U.nilIdeal x (Ideal.Quotient.eq_zero_iff_mem.mp hx))

def lift (U : BigCrystallineSite.Object p B J δ f) : A →ₐ[B] U.ring := (existsUnique_lift A g hg U).choose

theorem reduction (U : BigCrystallineSite.Object p B J δ f) :
    (Ideal.Quotient.mkₐ B U.ideal).comp (lift A g hg U) = EtaleResidue.residueMap A g hg U :=
  (existsUnique_lift A g hg U).choose_spec.1

theorem reduction_apply (U : BigCrystallineSite.Object p B J δ f) (a : A) :
    Ideal.Quotient.mk U.ideal (lift A g hg U a) = EtaleResidue.residueRingMap A g U a :=
  AlgHom.congr_fun (reduction A g hg U) a

theorem unique (U : BigCrystallineSite.Object p B J δ f) (l : A →ₐ[B] U.ring)
    (hl : (Ideal.Quotient.mkₐ B U.ideal).comp l = EtaleResidue.residueMap A g hg U) : l = lift A g hg U :=
  (existsUnique_lift A g hg U).choose_spec.2 l hl

theorem natural {U V : BigCrystallineSite.Object p B J δ f} (α : U ⟶ V) :
    (EtaleResidue.ambientMap α).comp (lift A g hg V) = lift A g hg U := by
  apply unique A g hg U
  apply AlgHom.ext
  intro a
  change Ideal.Quotient.mk U.ideal (α.ringMap (lift A g hg V a)) = EtaleResidue.residueRingMap A g U a
  have h : Ideal.Quotient.mk U.ideal (α.ringMap (lift A g hg V a)) =
      BigCrystallineSite.Object.quotientMap U V α.ringMap (Ideal.Quotient.mk V.ideal (lift A g hg V a)) := rfl
  rw [h, reduction_apply]
  exact RingHom.congr_fun (EtaleResidue.residue_natural A g α) a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.EtaleLift
