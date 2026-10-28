import OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.CrystallineEquivalence

/-! # Crystalline Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.CrystallineBasis

noncomputable section

/-! An actual finite basis and rank formula for original crystalline degree-zero cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] PeriodInvariants.WittAlgebraFunctor.wittAlgebra

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom] [Nonempty X.left]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom)

local notation "W" => WittVector p k
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionAlgebra.algebra k X
local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.integralCohomology p k X 0

def integralBasis : Module.Basis (Module.Free.ChooseBasisIndex k A) W M := by
  let := SmoothProper.GlobalFunctionAlgebra.nontrivial k X
  let := SmoothProper.GlobalFunctionAlgebra.module_finite k X hprojective
  let := SmoothProper.GlobalFunctionAlgebra.etale k X p hprojective
  exact (PeriodInvariants.FiniteEtaleWittModule.basis p k A).map
    (CrystallineEquivalence.integralEquiv p k X hprojective)

include hprojective in
theorem free : Module.Free W M := Module.Free.of_basis (integralBasis p k X hprojective)

include hprojective in
theorem finrank : Module.finrank (FractionRing W) (Witt.Crystalline.rationalCohomology p k X 0) =
    Module.finrank k A := by
  let := SmoothProper.GlobalFunctionAlgebra.module_finite k X hprojective
  let : Fintype (Module.Free.ChooseBasisIndex k A) := Fintype.ofFinite _
  have h₁ := Module.finrank_eq_card_basis ((integralBasis p k X hprojective).baseChange (FractionRing W))
  have h₂ := Module.finrank_eq_card_basis (Module.Free.chooseBasis k A)
  exact h₁.trans h₂.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.CrystallineBasis
