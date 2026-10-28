import OAI.NumberTheory.PadicHodge.GeometricComparison.CharacteristicDividedFrobenius
import OAI.NumberTheory.PadicHodge.GeometricComparison.WittPrime
import OAI.NumberTheory.PadicHodge.GeometricComparison.PrimeZero
import OAI.NumberTheory.PadicHodge.GeometricComparison.PrimeFieldSchemeFrobenius
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence

/-! # Crystalline Frobenius -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius

noncomputable section

/-! On the original level-zero crystalline site, p-power Frobenius
gives a natural frame morphism over the actual prime-field Frobenius. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
variable (p : ℕ) [Fact p.Prime] (Y : Over (Spec (CommRingCat.of (ZMod p))))

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "g" => Over.Hom.left (OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod p) Y)

theorem over_witt : g ≫ w = w := by
  simp only [IntegralComparison.Witt.Crystalline.wittStructureMap, ← Category.assoc, Over.w]

def postcompose := IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) g (over_witt p Y) 0

variable (U : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) 0)

theorem prime_zero : (p : U.obj.ring) = 0 := by
  simpa only [IntegralComparison.BoundedCrystalline.Site.property, Nat.zero_add, pow_one] using U.property

theorem quotient_prime_zero : (p : U.obj.ring ⧸ U.obj.ideal) = 0 := by
  have h := congrArg (Ideal.Quotient.mk U.obj.ideal) (prime_zero p Y U)
  simpa only [map_natCast, map_zero] using h

def map : (postcompose p Y).obj U ⟶ U := ObjectProperty.homMk
  { ringMap := CharacteristicDividedFrobenius.CharacteristicPDividedFrobenius.map p (prime_zero p Y U) U.obj.dividedPowers
    overBase := WittPrime.WittPrimeZeroFrobenius.comp p (prime_zero p Y U) U.obj.base
    overX := by
      change Spec.map (CommRingCat.ofHom
        (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.powerRingHom p Fact.out (U.obj.ring ⧸ U.obj.ideal) (quotient_prime_zero p Y U))) ≫
          U.obj.mapToX = U.obj.mapToX ≫ g
      exact (PrimeZero.PrimeZeroSpecFrobenius.naturality p (U.obj.ring ⧸ U.obj.ideal) (quotient_prime_zero p Y U)
        (IntegralComparison.Global.FrobeniusGeometry.scheme_prime_zero p (ZMod p) Y.hom) U.obj.mapToX).trans
          (congrArg (fun a => U.obj.mapToX ≫ a) (PrimeFieldSchemeFrobenius.Crystalline.schemeFrobenius_eq_finiteField p Y)) }

theorem map_apply (x : U.obj.ring) : (LevelZeroCrystallineFrobenius.map p Y U).hom.ringMap x = x ^ p := rfl

def transformation : postcompose p Y ⟶ 𝟭 _ where
  app := LevelZeroCrystallineFrobenius.map p Y
  naturality := by
    intro U V α
    apply ObjectProperty.hom_ext
    apply IntegralComparison.BigCrystallineSite.Object.Hom.ext
    apply DividedPowers.DPMorphism.ext
    funext x
    exact map_pow α.hom.ringMap.toRingHom x p

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius
