import OAI.NumberTheory.PadicHodge.IntegralComparison.EmptyPolynomialAlgebra
import OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteEtaleWittLift
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittVanishing

/-! # Bounded Crystalline -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.BoundedCrystalline

noncomputable section

/-! The original bounded crystalline cohomology of a finite étale algebra vanishes in every positive degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] PeriodInvariants.WittAlgebraFunctor.wittAlgebra

universe u

variable (p : ℕ) [Fact p.Prime] (k A : Type u) [Field k] [CommRing A] [Algebra k A]
  [CharP k p] [PerfectRing k p] [Nontrivial A] [Module.Finite k A] [Algebra.Etale k A]

local notation "W" => WittVector p k
local notation "WA" => WittVector p A
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k A)

theorem vanishing (n i : ℕ) : Subsingleton (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
    (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n (i + 1)) := by
  let := PeriodInvariants.FiniteEtaleWittModule.targetCharP p k A
  let := PeriodInvariants.FiniteEtaleWittModule.targetPerfect p k A
  let := PeriodInvariants.FiniteEtaleWittLift.etale p k A
  let := PeriodInvariants.FiniteEtaleWittModule.flat p k A
  let := EmptyPolynomialAlgebra.algebra W WA
  let := EmptyPolynomialAlgebra.tower W WA
  let := EmptyPolynomialAlgebra.etale W WA
  exact BoundedSmooth.WittVanishing.cohomology_zero p k WA A PEmpty.{u + 1}
    WittVector.constantCoeff (WittVector.constantCoeff_surjective p) WittVector.ker_constantCoeff
    (fun _ => rfl) n (i + 1) (by simp)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.BoundedCrystalline
