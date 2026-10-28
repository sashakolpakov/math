import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ConstantSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.NilLifting

/-! # Etale Residue -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.EtaleResidue

noncomputable section

/-! Residue maps from an actual affine factor of the scheme on the original crystalline site. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
  (A : Type u) [CommRing A] [Algebra B A]
  (g : X ⟶ Spec (CommRingCat.of A))
  (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap B A)) = f)

abbrev objectAlgebra (U : BigCrystallineSite.Object p B J δ f) : Algebra B U.ring := U.base.toAlgebra

attribute [local instance] objectAlgebra

def residueRingMap (U : BigCrystallineSite.Object p B J δ f) : A →+* U.ring ⧸ U.ideal :=
  (Spec.preimage (U.mapToX ≫ g)).hom

omit [Algebra B A] in
theorem residueRingMap_spec (U : BigCrystallineSite.Object p B J δ f) :
    Spec.map (CommRingCat.ofHom (residueRingMap A g U)) = U.mapToX ≫ g := Spec.map_preimage _

include hg in
theorem residueRingMap_base (U : BigCrystallineSite.Object p B J δ f) :
    (residueRingMap A g U).comp (algebraMap B A) = (Ideal.Quotient.mk U.ideal).comp U.base := by
  have h := (congrArg (fun t => t ≫ Spec.map (CommRingCat.ofHom (algebraMap B A)))
    (residueRingMap_spec A g U)).trans
      ((Category.assoc _ _ _).trans ((congrArg (fun t => U.mapToX ≫ t) hg).trans U.overBase))
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

def residueMap (U : BigCrystallineSite.Object p B J δ f) : A →ₐ[B] U.ring ⧸ U.ideal where
  __ := residueRingMap A g U
  commutes' b := RingHom.congr_fun (residueRingMap_base A g hg U) b

def ambientMap {U V : BigCrystallineSite.Object p B J δ f} (α : U ⟶ V) : V.ring →ₐ[B] U.ring where
  __ := α.ringMap.toRingHom
  commutes' b := RingHom.congr_fun α.overBase b

omit [Algebra B A] in
theorem residue_natural {U V : BigCrystallineSite.Object p B J δ f} (α : U ⟶ V) :
    (BigCrystallineSite.Object.quotientMap U V α.ringMap).comp (residueRingMap A g V) = residueRingMap A g U := by
  have h : Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap U V α.ringMap)) ≫
      Spec.map (CommRingCat.ofHom (residueRingMap A g V)) =
        Spec.map (CommRingCat.ofHom (residueRingMap A g U)) := by
    rw [residueRingMap_spec, residueRingMap_spec, ← Category.assoc, α.overX]
  rw [← Spec.map_comp] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.EtaleResidue
