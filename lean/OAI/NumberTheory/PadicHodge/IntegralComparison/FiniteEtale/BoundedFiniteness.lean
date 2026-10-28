import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.BoundedCrystalline
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.DeRham
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PerfectWittQuotient
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.ModuleHomology

/-! # Bounded Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.BoundedFiniteness

noncomputable section

/-! Actual bounded crystalline cohomology of a finite étale algebra over a finite field consists of finite groups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] PeriodInvariants.WittAlgebraFunctor.wittAlgebra

universe u

variable (p : ℕ) [Fact p.Prime] (k A : Type u) [Field k] [Fintype k] [CommRing A] [Algebra k A]
  [CharP k p] [Nontrivial A] [Module.Finite k A] [Algebra.Etale k A]

local notation "W" => WittVector p k
local notation "WA" => WittVector p A
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k A)

theorem finite (n i : ℕ) : Finite (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
    (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n i) := by
  let := PeriodInvariants.FiniteEtaleWittModule.targetCharP p k A
  let := PeriodInvariants.FiniteEtaleWittModule.targetPerfect p k A
  let := PeriodInvariants.FiniteEtaleWittLift.etale p k A
  let := PeriodInvariants.FiniteEtaleWittModule.flat p k A
  let := EmptyPolynomialAlgebra.algebra W WA
  let := EmptyPolynomialAlgebra.tower W WA
  let := EmptyPolynomialAlgebra.etale W WA
  let : Finite A := Module.finite_of_finite k
  let : Finite (SmoothWitt.FrameRing.Ring p WA n) := IntegralComparison.Finite.PerfectWittQuotient.finite p A n
  let An := SmoothWitt.FrameRing.Ring p WA n
  let : Algebra W An := (SmoothWitt.FrameRing.base p k WA n).toAlgebra
  let : Finite ((Fin i → An) →₀ An) :=
    Finite.of_injective (fun x : (Fin i → An) →₀ An => (x : (Fin i → An) → An)) DFunLike.coe_injective
  let : Finite (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form W An i) :=
    Finite.of_surjective (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations W An i).mkQ
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations W An i).mkQ_surjective
  let : Finite ((SmoothWitt.DeRham.Comparison.deRhamComplex p k WA n).X i) :=
    inferInstanceAs (Finite (ULift.{u + 2} (ULift.{u + 1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form W An i))))
  let := IntegralComparison.Finite.ModuleHomology.complex R (SmoothWitt.DeRham.Comparison.deRhamComplex p k WA n) i
  exact Finite.of_injective _ (SmoothWitt.DeRham.Comparison.homologyIso p k WA A PEmpty.{u + 1}
    WittVector.constantCoeff (WittVector.constantCoeff_surjective p) WittVector.ker_constantCoeff
    (fun _ => rfl) n i).symm.toLinearEquiv.injective

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.BoundedFiniteness
