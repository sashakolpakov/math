import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.BoundedFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.FiniteInverseLimit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.Crystalline

/-! # Crystalline Inverse Limit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CrystallineInverseLimit

noncomputable section

/-! The original integral crystalline cohomology is the inverse limit of its finite bounded Ext groups in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

include hprojective in
theorem inclusion_mono (i : ℕ) : Mono (HomologicalComplex.homologyMap
    (Crystalline.ResolutionComplexExact.sequence (p := p) (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X)).f i) := by
  cases i with
  | zero =>
    exact ShortExactHomologyKernel.mono_zero _
      (Crystalline.ResolutionComplexExact.shortExact (p := p) (J := Ideal.span {(p : WittVector p k)})
        (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X))
  | succ i =>
    let (n : ℕ) : Finite (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
        (J := Ideal.span {(p : WittVector p k)})
        (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n i) :=
      BoundedFiniteness.finite_type p k X hprojective n i
    exact Crystalline.FiniteLevelKernel.inclusion_mono_succ (Witt.Crystalline.wittStructureMap p k X) i

def bigCompatibleEquiv (i : ℕ) :
    BigCrystallineCohomology.Cohomology (p := p) (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) i ≃ₗ[R]
        Crystalline.CohomologyDifference.compatible (p := p) (J := Ideal.span {(p : WittVector p k)})
          (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) i := by
  let := inclusion_mono p k X hprojective i
  exact Crystalline.FiniteInverseLimit.compatibleLinearEquiv (Witt.Crystalline.wittStructureMap p k X) i

def compatibleEquiv (i : ℕ) : Witt.Crystalline.integralCohomology p k X i ≃ₗ[R]
    Crystalline.CohomologyDifference.compatible (p := p) (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) i :=
  (Global.Crystalline.Comparison.integralEquiv p k X i).symm.trans (bigCompatibleEquiv p k X hprojective i)

def limitEquiv (i : ℕ) : Witt.Crystalline.integralCohomology p k X i ≃ₗ[R]
    (limit (Crystalline.FiniteInverseLimit.diagram (p := p) (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) i) : ModuleCat.{u + 2} R) :=
by
  let := inclusion_mono p k X hprojective i
  exact (Global.Crystalline.Comparison.integralEquiv p k X i).symm.trans
    (Crystalline.FiniteInverseLimit.linearEquiv (p := p)
      (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
      (Witt.Crystalline.wittStructureMap p k X) i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CrystallineInverseLimit
