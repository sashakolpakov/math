import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.ReferenceCupNaturality

/-! # Cup Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.CupNaturality.ReferenceIntegral

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (hX : Projectivity.Construction.ProjectiveOver k X.hom)
abbrev natural (f : X ⟶ X) (i j : ℕ)
    (x : Witt.Crystalline.integralCohomology p k X i)
    (y : Witt.Crystalline.integralCohomology p k X j) := by
  have h := Balanced.RationalCupNaturality.integral_cup_natural p k X X f hX hX i j x y
  rw [CrystallineCupNaturality.integralPullback_eq,
    CrystallineCupNaturality.integralPullback_eq,
    CrystallineCupNaturality.integralPullback_eq] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.CupNaturality.ReferenceIntegral
