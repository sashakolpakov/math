import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.ReferenceUnitNaturality

/-! # Scalar Cup Compatibility -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.ScalarCupCompatibility

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (hX : Projectivity.Construction.ProjectiveOver k X.hom)
local notation "W" => WittVector p k
local notation "F" => FractionRing (WittVector p k)
local notation "I" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.integralCohomology p k X
def endomorphism (f : X ⟶ X) (n : ℕ) : Module.End F (F ⊗[W] I n) :=
  PeriodInvariants.CrystallinePullback.rationalPullback p k f n
abbrev unit (f : X ⟶ X) := by
  have h := Balanced.ReferenceUnitNaturality.Reference.one_natural p k X X f hX hX
  dsimp only [Balanced.RationalCupUnit.one] at h
  exact h
abbrev cup (f : X ⟶ X) (i j : ℕ)
    (x : Witt.Crystalline.rationalCohomology p k X i)
    (y : Witt.Crystalline.rationalCohomology p k X j) := by
  have h := Balanced.ReferenceCupNaturality.Reference.cup_natural p k X X f hX hX i j x y
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.ScalarCupCompatibility
