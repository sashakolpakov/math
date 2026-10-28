import OAI.AlgebraicTopology.Kunneth.ManifoldComparisonCochain
import OAI.AlgebraicTopology.Products.CupCohomology

/-! # Manifold Integration Cup -/

namespace OAI.AlgebraicTopology.Kunneth.ManifoldIntegrationCup

noncomputable section

/-! Multiplicativity of the original integration map on actual smooth-singular cohomology. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory OAI.AlgebraicTopology.Products.CupCohomology
open scoped _root_.Manifold ContDiff

namespace Constructions

def cochainCocycleDegreeCast (K : SSet.{0}) {n m : ℕ} (h : n = m)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of ℂ ℂ)) n) :
    Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of ℂ ℂ)) m := h ▸ c

theorem cochainCocycleDegreeCast_val (K : SSet.{0}) {n m : ℕ} (h : n = m)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of ℂ ℂ)) n) :
    (cochainCocycleDegreeCast K h c).val = Products.Cup.cochainCast K (ModuleCat.of ℂ ℂ) h c.val := by
  subst m
  rfl

theorem cochainClass_eq_of_cast (K : SSet.{0}) {n m : ℕ} (h : n = m)
    (c d : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of ℂ ℂ)) n)
    (he : Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of ℂ ℂ)) m (cochainCocycleDegreeCast K h c) =
      Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of ℂ ℂ)) m (cochainCocycleDegreeCast K h d)) :
    Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of ℂ ℂ)) n c =
      Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of ℂ ℂ)) n d := by
  subst m
  exact he

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {p q : ℕ}

theorem smoothSimplexIntegrationCocycle_cast {n m : ℕ} (h : n = m)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n) :
    DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle E M m (ClosedManifoldWedge.Constructions.closedManifoldDegreeCast h a) =
      cochainCocycleDegreeCast (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet h
        (DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle E M n a) := by
  subst m
  rfl

theorem integrationCup_normalized (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M p) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) (q + p)
      (DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle E M (q + p)
        (ClosedManifoldWedge.Constructions.closedManifoldDegreeCast (Nat.add_comm p q) (ClosedManifoldWedge.Constructions.closedManifoldWedge a b))) =
    Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) (q + p)
      (cochainCocycleDegreeCast (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (Nat.add_comm p q)
        (Products.CupCohomology.cocycleCupWith (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (LinearMap.mul ℂ ℂ) p q
          (DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle E M p a)
          (DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle E M q b))) := by
  cases p with
  | zero =>
      apply congrArg (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) q)
      apply Subtype.ext
      rw [cochainCocycleDegreeCast_val]
      exact sub_eq_zero.mp (ManifoldComparisonCochain.Constructions.manifoldIntegrationDifference_closed_zero a b)
  | succ p =>
      apply (Cohomology.Singular.Representatives.cochainClass_eq_iff_exists_succ (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M)
        (q + p) _ _).mpr
      refine ⟨ManifoldComparisonCochain.Constructions.manifoldComparisonCochain a.val b, ?_⟩
      rw [cochainCocycleDegreeCast_val]
      exact (ManifoldComparisonCochain.Constructions.manifoldIntegrationDifference_closed_succ a b).symm

/-- Integration of the actual exterior product represents the actual cup product. -/
theorem smoothSimplexIntegrationClass_wedge
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M p) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) (p + q)
      (DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle E M (p + q) (ClosedManifoldWedge.Constructions.closedManifoldWedge a b)) =
      Products.CupCohomology.cohomologyCup (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet p q
        (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) p
          (DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle E M p a))
        (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) q
          (DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle E M q b)) := by
  rw [Products.CupCohomology.cohomologyCupWith_class_class]
  apply cochainClass_eq_of_cast (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (Nat.add_comm p q)
  rw [← smoothSimplexIntegrationCocycle_cast]
  exact integrationCup_normalized a b

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.ManifoldIntegrationCup
