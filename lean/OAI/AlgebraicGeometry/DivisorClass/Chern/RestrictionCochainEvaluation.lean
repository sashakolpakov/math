import OAI.AlgebraicTopology.Cohomology.Singular.Chains
import OAI.AlgebraicTopology.Cohomology.Singular.Coefficients

/-! # Restriction Cochain Evaluation -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.RestrictionCochainEvaluation

noncomputable section

/-! Scalar restriction preserves actual evaluation on every singular simplex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type} [CommRing R] [CommRing S]

theorem singularCochainsRestrictScalarsIso_hom_evaluation (f : R →+* S)
    (M : ModuleCat.{0} S) (X : TopCat.{0}) {n : ℕ} (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    (AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso f M X).hom.f n ≫
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) ((ModuleCat.restrictScalars f).obj M) s =
        (ModuleCat.restrictScalars f).map (AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) M s) := by
  apply Quiver.Hom.op_inj
  change (TopCat.toSSet.obj X).ιChainComplex s ≫
    sigmaComparison (ModuleCat.restrictScalars f).op (fun _ : (TopCat.toSSet.obj X) _⦋n⦌ => op M) =
      (ModuleCat.restrictScalars f).op.map ((TopCat.toSSet.obj X).ιChainComplex s)
  exact ι_comp_sigmaComparison _ _ _

theorem singularCochainsRestrictScalarsIso_inv_evaluation (f : R →+* S)
    (M : ModuleCat.{0} S) (X : TopCat.{0}) {n : ℕ} (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    (AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso f M X).inv.f n ≫
      (ModuleCat.restrictScalars f).map (AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) M s) =
        AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) ((ModuleCat.restrictScalars f).obj M) s := by
  rw [← singularCochainsRestrictScalarsIso_hom_evaluation f M X s, ← Category.assoc]
  have h := congrArg (fun g => g.f n) (AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso f M X).inv_hom_id
  rw [show (AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso f M X).inv.f n ≫
      (AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso f M X).hom.f n = 𝟙 _ from h, Category.id_comp]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.RestrictionCochainEvaluation
