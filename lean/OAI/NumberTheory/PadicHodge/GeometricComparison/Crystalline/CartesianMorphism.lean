import OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.QuotientPullback
import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

/-! # Cartesian Morphism -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.CartesianMorphism.CrystallineCartesianMorphism

noncomputable section

/-! Extending the defining ideal exactly makes a crystalline morphism
cartesian on its ambient and closed schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem quotient_pullback {A S : Type u} [CommRing A] [CommRing S]
    (I : Ideal A) (J : Ideal S) (f : A →+* S) (hle : I ≤ J.comap f) (heq : I.map f = J) :
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.quotientMap J f hle)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) (Spec.map (CommRingCat.ofHom f)) := by
  subst J
  exact IntegralComparison.Quotient.QuotientPullback.schemePullback I f

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
  {U V : IntegralComparison.BigCrystallineSite.Object p B J δ f} (α : U ⟶ V)

theorem cartesian (h : V.ideal.map α.ringMap.toRingHom = U.ideal) :
    IsPullback (IntegralComparison.BigCrystallineSite.Object.closed.map α) (IntegralComparison.BigCrystallineSite.Object.closedImmersion.app U)
      (IntegralComparison.BigCrystallineSite.Object.closedImmersion.app V) (IntegralComparison.BigCrystallineSite.Object.ambient.map α) :=
  quotient_pullback V.ideal U.ideal α.ringMap.toRingHom
    (Ideal.map_le_iff_le_comap.mp α.ringMap.ideal_comp) h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.CartesianMorphism.CrystallineCartesianMorphism
