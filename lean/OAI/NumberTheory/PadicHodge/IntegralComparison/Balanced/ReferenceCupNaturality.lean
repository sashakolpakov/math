import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.RationalCupNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.CrystallineCupNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.FrobeniusPullback

/-! # Reference Cup Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.ReferenceCupNaturality.Reference

noncomputable section

/-! The actual rational crystalline cup is preserved by the original
geometric pullback and by the original finite-field Frobenius operator. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X Y : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  [IsProper Y.hom] [Smooth Y.hom] (g : X ⟶ Y)

open OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.CrystallineCupNaturality (pullback_eq)

variable (hX : Projectivity.Construction.ProjectiveOver k X.hom) (hY : Projectivity.Construction.ProjectiveOver k Y.hom)

include p k X Y g hX hY in
abbrev cup_natural (i j : ℕ) (x : Witt.Crystalline.rationalCohomology p k Y i)
    (y : Witt.Crystalline.rationalCohomology p k Y j) := by
  have h := RationalCupNaturality.cup_natural p k X Y g hX hY i j x y
  rw [Reference.CrystallineCupNaturality.integralPullback_eq,
    Reference.CrystallineCupNaturality.integralPullback_eq,
    Reference.CrystallineCupNaturality.integralPullback_eq] at h
  exact h

include p k X hX in
abbrev frobenius_cup (a : ℕ) (hcard : Fintype.card k = p ^ a)
    (i j : ℕ) (x : Witt.Crystalline.rationalCohomology p k X i) (y : Witt.Crystalline.rationalCohomology p k X j) := by
  have h := cup_natural p k X X (FrobeniusPullback.Q.endomorphism p k X a hcard)
    hX hX i j x y
  have hf (m : ℕ) := FrobeniusPullback.Q.rational p k X a hcard m
  unfold PeriodInvariants.CrystallinePullback.rationalPullback at hf
  rw [← hf (i + j), ← hf i, ← hf j] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.ReferenceCupNaturality.Reference
