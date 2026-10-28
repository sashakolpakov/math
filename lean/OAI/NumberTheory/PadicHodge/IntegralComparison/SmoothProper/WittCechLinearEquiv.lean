import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTransitionData

/-! # Witt Cech Linear Equiv -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechLinearEquiv

noncomputable section

/-! Native Witt frame Čech cohomology is linearly equivalent to the original bounded crystalline Ext. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTransitionData

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

def liftedHomologyIso (n i : ℕ) :
    (ModuleCat.uliftFunctor.{u + 2, u + 1} R).obj ((WittCechTransitionData.complex p k X n).homology i) ≅ ModuleCat.of R
      (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := Ideal.span {(p : WittVector p k)})
        (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n i) :=
  (((WittCechTransitionData.complex p k X n).sc i).mapHomologyIso (ModuleCat.uliftFunctor.{u + 2, u + 1} R)).symm ≪≫
    WittCechCohomology.homologyIso p k X n i

def equivalence (n i : ℕ) : (WittCechTransitionData.complex p k X n).homology i ≃ₗ[R]
    BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n i :=
  ULift.moduleEquiv.symm.trans (liftedHomologyIso p k X n i).toLinearEquiv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechLinearEquiv
