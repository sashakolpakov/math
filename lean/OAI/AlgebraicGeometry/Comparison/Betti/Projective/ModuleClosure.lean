import OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechExact
import OAI.AlgebraicGeometry.Comparison.Betti.NaturalCoproduct
import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.Isomorphism
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Module Closure -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.ModuleClosure.Dolbeault

noncomputable section

/-! The actual projective comparison is stable under finite sums, isomorphisms, and exact cokernels. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def projectiveModuleComparisonIsomorphism (n : ℕ) (M : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Modules) : Prop :=
  QuasiIso (ModuleFunctor.Dolbeault.projectiveModuleOriginalCechMap n M)

theorem projectiveModuleComparisonIsomorphism_twist (n : ℕ) (j : Fin (n + 2)) (d : ℤ) :
    projectiveModuleComparisonIsomorphism (n + 1) (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d) := by
  change QuasiIso (ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveTwistOriginalCechMap (n + 1) j d)
  rw [quasiIso_iff]
  intro r
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact ProjectiveTwist.Isomorphism.Dolbeault.projectiveOriginalComparison_all_degrees_isIso n j d r

theorem projectiveModuleComparisonIsomorphism_of_iso (n : ℕ)
    {M N : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Modules} (e : M ≅ N) (hM : projectiveModuleComparisonIsomorphism n M) :
    projectiveModuleComparisonIsomorphism n N := by
  let : QuasiIso (ModuleFunctor.Dolbeault.projectiveModuleOriginalCechMap n M) := hM
  change QuasiIso _
  rw [quasiIso_iff]
  intro r
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := homologyFunctor AddCommGrpCat.{0} (.up ℕ) r
  let τ := Functor.whiskerRight (ModuleFunctor.Dolbeault.projectiveModuleCechComparison n) H
  let : IsIso (τ.app M) := inferInstanceAs (IsIso (homologyMap (ModuleFunctor.Dolbeault.projectiveModuleOriginalCechMap n M) r))
  exact NaturalCoproduct.Category.naturalComparison_isIso_of_iso τ e

theorem projectiveModuleComparisonIsomorphism_finiteCoproduct (n : ℕ) {ι : Type} [Fintype ι]
    (M : ι → (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Modules) (hM : ∀ i, projectiveModuleComparisonIsomorphism n (M i)) :
    projectiveModuleComparisonIsomorphism n (∐ M) := by
  change QuasiIso _
  rw [quasiIso_iff]
  intro r
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := homologyFunctor AddCommGrpCat.{0} (.up ℕ) r
  let τ := Functor.whiskerRight (ModuleFunctor.Dolbeault.projectiveModuleCechComparison n) H
  let : ∀ i, IsIso (τ.app (M i)) := fun i => by
    let : QuasiIso (ModuleFunctor.Dolbeault.projectiveModuleOriginalCechMap n (M i)) := hM i
    exact inferInstanceAs (IsIso (homologyMap (ModuleFunctor.Dolbeault.projectiveModuleOriginalCechMap n (M i)) r))
  exact NaturalCoproduct.Category.naturalComparison_coproduct_isIso τ M

theorem projectiveModuleComparisonIsomorphism_cokernel (n : ℕ)
    (S : ShortComplex (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Modules)
    (hA : (S.map (ModuleFunctor.Dolbeault.projectiveAlgebraicModuleCechFunctor n)).ShortExact)
    (hB : (S.map (ModuleFunctor.Dolbeault.projectiveAnalyticModuleCechFunctor n)).ShortExact)
    (h₁ : projectiveModuleComparisonIsomorphism n S.X₁)
    (h₂ : projectiveModuleComparisonIsomorphism n S.X₂) :
    projectiveModuleComparisonIsomorphism n S.X₃ := by
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃
    (S.mapNatTrans (ModuleFunctor.Dolbeault.projectiveModuleCechComparison n)) hA hB h₁ h₂

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.ModuleClosure.Dolbeault
