import OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.SmoothLift
import OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.IdealPDMap

/-! # Level Frame -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.LevelFrame

noncomputable section

/-!
# IntegralComparison: the original smooth affine chart is a frame at crystalline level zero
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.Frobenius

universe u

variable (p : ℕ) [Fact p.Prime] (k C : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [Algebra k C]

omit [Fact p.Prime] [Fintype k] in
include k in
theorem prime_zero : (p : C) = 0 := by
  simpa only [map_natCast, map_zero] using congrArg (algebraMap k C) (CharP.cast_eq_zero k p)

def frame : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) where
  ring := CommRingCat.of C
  base := Polynomial.Frobenius.coefficientReduction p k C
  ideal := ⊥
  dividedPowers := dividedPowersBot C
  baseCompatible := (DividedPower.Transfer.mapToBot _ (Polynomial.Frobenius.coefficientReduction p k C) (by
    apply Ideal.span_le.mpr
    rintro a (rfl : a = _)
    change Polynomial.Frobenius.coefficientReduction p k C (p : WittVector p k) = 0
    rw [map_natCast, prime_zero p k C])).isDPMorphism
  primeNilpotent := ⟨1, (pow_one (p : C)).trans (prime_zero p k C)⟩
  nilIdeal := fun a ha => by rw [Ideal.mem_bot.mp ha]; exact ⟨1, pow_one 0⟩
  mapToX := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal C)))
  overBase := by
    rw [Crystalline.Presentation.affine_wittStructureMap]
    rfl

def boundedFrame : BoundedCrystalline.Site.Objects (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) 0 :=
  ⟨frame p k C, (pow_one (p : C)).trans (prime_zero p k C)⟩

variable (U : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)))

def mapOfLift (l : C →+* U.ring)
    (hl : (Ideal.Quotient.mk U.ideal).comp l = BigCrystallineCover.closedRingMap p k C U)
    (hb : l.comp (Polynomial.Frobenius.coefficientReduction p k C) = U.base) : U ⟶ frame p k C where
  ringMap := Zero.IdealPDMap.map U.dividedPowers l
  overBase := hb
  overX := by
    change Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap U (frame p k C)
      (Zero.IdealPDMap.map U.dividedPowers l))) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal C))) = U.mapToX
    rw [← Spec.map_comp]
    have hc : (BigCrystallineSite.Object.quotientMap U (frame p k C) (Zero.IdealPDMap.map U.dividedPowers l)).comp
        (Ideal.Quotient.mk (⊥ : Ideal C)) = BigCrystallineCover.closedRingMap p k C U := hl
    change Spec.map (CommRingCat.ofHom ((BigCrystallineSite.Object.quotientMap U (frame p k C)
      (Zero.IdealPDMap.map U.dividedPowers l)).comp (Ideal.Quotient.mk (⊥ : Ideal C)))) = U.mapToX
    rw [hc]
    exact BigCrystallineCover.closedRingMap_spec p k C U

theorem exists_map [Algebra.Smooth k C] (h : (p : U.ring) = 0) : Nonempty (U ⟶ frame p k C) := by
  obtain ⟨l, hl, hb⟩ := SmoothLift.exists_lift p k C U h
  refine ⟨mapOfLift p k C U l hl ?_⟩
  change l.comp ((algebraMap k C).comp WittVector.constantCoeff) = U.base
  rw [← RingHom.comp_assoc, hb, Bounded.WittBase.residueBase_constantCoeff]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.LevelFrame
