import OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.CupNaturality

/-! # Scalar Cup Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.ScalarCupNaturality

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
  (PeriodInvariants.CrystallinePullback.integralPullback p k f n).baseChange F
local notation "fS" => OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.ScalarCupNaturality.endomorphism p k X
theorem natural (f : X ⟶ X) (i j : ℕ) (x : F ⊗[W] I i) (y : F ⊗[W] I j) :
    fS f (i + j) (BilinearScalarExtension.map F
      (Balanced.RationalCrystallineCup.integralCup p k X hX i j) x y) =
    BilinearScalarExtension.map F (Balanced.RationalCrystallineCup.integralCup p k X hX i j)
      (fS f i x) (fS f j y) := by
  dsimp only [endomorphism]
  exact BilinearScalarExtension.map_natural F
    (Balanced.RationalCrystallineCup.integralCup p k X hX i j)
    (Balanced.RationalCrystallineCup.integralCup p k X hX i j)
    (PeriodInvariants.CrystallinePullback.integralPullback p k f i)
    (PeriodInvariants.CrystallinePullback.integralPullback p k f j)
    (PeriodInvariants.CrystallinePullback.integralPullback p k f (i + j))
    (CupNaturality.ReferenceIntegral.natural p k X hX f i j) x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.ScalarCupNaturality
