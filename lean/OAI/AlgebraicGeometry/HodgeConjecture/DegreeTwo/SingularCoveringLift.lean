import OAI.AlgebraicTopology.Cohomology.Singular.Formulas
import Mathlib.Topology.Homotopy.Lifting
import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-! # Singular Covering Lift -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularCoveringLift.Constructions.SingularCovering

noncomputable section

/-!
# DegreeTwo: singular cochains and covering projections

Every actual singular simplex lifts through a surjective covering map.
Consequently pullback is injective on singular cochains, in every degree.
This will let the lattice-period comparison test equations on the vector
space covering without losing cochain information.
-/

open _root_.CategoryTheory Opposite
open scoped Simplicial

open OAI.AlgebraicTopology.Cohomology.Singular.Formulas

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : IsCoveringMap f)
  (hs : Function.Surjective f)

include hf hs

/-- Every continuous standard simplex has an actual continuous lift. -/
theorem exists_simplex_lift (n : ℕ) (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), Y)) :
    ∃ τ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X), (f : X → Y) ∘ τ = σ := by
  let S := Convexity.StdSimplex ℝ (Fin (n + 1))
  let a : S := Convexity.StdSimplex.single 0
  let coord : S → Fin (n + 1) → ℝ := fun x => x.weights
  have hconv : Convex ℝ (Set.range coord) := by
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩ c d hc hd hcd
    refine ⟨Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.ofCoordinates (c • coord u + d • coord v) ?_ ?_, ?_⟩
    · intro i
      exact add_nonneg (mul_nonneg hc (u.weights_nonneg i))
        (mul_nonneg hd (v.weights_nonneg i))
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, coord, Convexity.StdSimplex.total_of_fintype, mul_one, hcd]
    · funext i
      simp [coord, Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.ofCoordinates]
  let e : S ≃ₜ Set.range coord :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).toHomeomorph
  let : ContractibleSpace (Set.range coord) :=
    hconv.contractibleSpace ⟨coord a, ⟨a, rfl⟩⟩
  let : LocallyPathConnectedSpace (Set.range coord) := hconv.locallyPathConnectedSpace
  let : ContractibleSpace S := e.contractibleSpace
  let : LocallyPathConnectedSpace S := e.symm.locallyPathConnectedSpace
  obtain ⟨x, hx⟩ := hs (σ a)
  obtain ⟨τ, hτ, _⟩ := hf.existsUnique_continuousMap_lifts σ a x hx
  exact ⟨τ, hτ.2⟩

/-- The map on genuine singular simplices of a surjective covering is
surjective in each simplicial degree. -/
theorem singularSimplex_map_surjective (n : ℕ) :
    Function.Surjective ((TopCat.toSSet.map f).app (op ⦋n⦌)) := by
  intro s
  let σ := (TopCat.toSSetObjEquiv Y (op ⦋n⦌)) s
  obtain ⟨τ, hτ⟩ := exists_simplex_lift f hf hs n σ
  refine ⟨(TopCat.toSSetObjEquiv X (op ⦋n⦌)).symm τ, ?_⟩
  apply (TopCat.toSSetObjEquiv Y (op ⦋n⦌)).injective
  ext z
  change f (τ z) = σ z
  exact congrFun hτ z

/-- Pullback by a surjective covering is injective on actual singular
cochains; no assertion of injectivity on cohomology is made. -/
theorem singularPullback_injective {R : Type} [Ring R] (M : ModuleCat.{0} R) (n : ℕ) :
    Function.Injective ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M f).f n) := by
  intro a b hab
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj Y) M n).toLinearEquiv.injective
  ext s
  obtain ⟨t, rfl⟩ := singularSimplex_map_surjective f hf hs n s
  have h := congrArg
    (fun c => (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M n).hom c t) hab
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M n).hom
      ((AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback M (TopCat.toSSet.map f)).f n a) t =
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M n).hom
      ((AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback M (TopCat.toSSet.map f)).f n b) t at h
  rw [AlgebraicTopology.Cohomology.Singular.Formulas.degreewiseFunctionIso_pullback, AlgebraicTopology.Cohomology.Singular.Formulas.degreewiseFunctionIso_pullback] at h
  exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularCoveringLift.Constructions.SingularCovering
