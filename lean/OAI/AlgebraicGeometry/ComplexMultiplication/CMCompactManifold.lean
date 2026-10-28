import OAI.AlgebraicTopology.Products.CapBoundary
import OAI.AlgebraicTopology.Duality.Poincare.Manifold
import OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient
import OAI.AlgebraicTopology.Singular.Cohomology
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # CM Compact Manifold -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CMCompactManifold.CompactManifoldFiniteness

noncomputable section

/-! # Finiteness on the original singular chain objects

The finite-cap-image argument is adapted from `Hodge.KunnethProofs.CapFiniteness`.
The existing genuine compact complex manifold cap-duality theorem supplies surjectivity.
No alternate geometric realization or supplied finite-dimensional model is used.
-/

open _root_.CategoryTheory Limits
open OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient OAI.AlgebraicTopology.Products.CapBoundary OAI.AlgebraicTopology.Duality.Poincare.Manifold
open scoped Simplicial _root_.Manifold

section Cap

variable {k : Type} [Field k]

private def cycleRetraction (C : ChainComplex (ModuleCat.{0} k) ℕ) (n : ℕ) :
    C.X n →ₗ[k] AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C n := (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C n).subtype.leftInverse

private theorem cycleRetraction_cycle (C : ChainComplex (ModuleCat.{0} k) ℕ)
    (n : ℕ) (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C n) : cycleRetraction C n z.val = z :=
  LinearMap.leftInverse_apply_of_inj (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C n).ker_subtype z

private theorem simplexChain_span (K : SSet.{0}) (n : ℕ) :
    Submodule.span k (Set.range (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := k) K (n := n))) = ⊤ := by
  let S := Submodule.span k (Set.range (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := k) K (n := n)))
  have h : S.mkQ = 0 := by
    apply AlgebraicTopology.Cohomology.Singular.ChainDual.chainFunctional_ext K (ModuleCat.of k (((AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains K).X n) ⧸ S))
    intro s
    exact (Submodule.Quotient.mk_eq_zero S).mpr (Submodule.subset_span ⟨s, rfl⟩)
  apply Submodule.eq_top_iff'.mpr
  intro z
  exact (Submodule.Quotient.mk_eq_zero S).mp (LinearMap.congr_fun h z)

private theorem exists_finite_cap_container (K : SSet.{0}) (p q : ℕ)
    (z : (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X (p + q)) :
    ∃ S : Submodule k ((AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X q),
      S.FG ∧ ∀ c, AlgebraicTopology.Products.Cap.cap K p q c z ∈ S := by
  have hz : z ∈ Submodule.span k (Set.range (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := k) K (n := p + q))) := by
    rw [simplexChain_span]
    trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    refine ⟨k ∙ AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := k) K (AlgebraicTopology.Products.SimplexFaceIdentities.backFace K p q s),
      Submodule.fg_span_singleton _, ?_⟩
    intro c
    rw [AlgebraicTopology.Products.Cap.cap_simplex]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  | zero =>
    refine ⟨⊥, Submodule.fg_bot, ?_⟩
    intro c
    simp only [map_zero, Submodule.zero_mem]
  | add x y _ _ hx hy =>
    obtain ⟨S, hS, hx⟩ := hx
    obtain ⟨T, hT, hy⟩ := hy
    refine ⟨S ⊔ T, hS.sup hT, ?_⟩
    intro c
    rw [map_add]
    exact Submodule.add_mem _
      ((show S ≤ S ⊔ T from le_sup_left) (hx c))
      ((show T ≤ S ⊔ T from le_sup_right) (hy c))
  | smul r x _ hx =>
    obtain ⟨S, hS, hx⟩ := hx
    refine ⟨S, hS, ?_⟩
    intro c
    rw [map_smul]
    exact S.smul_mem r (hx c)

/-- A surjective actual cap product has finite-dimensional target homology. -/
theorem finite_homology_of_cap_surjective (K : SSet.{0}) (p q : ℕ)
    (z : (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).homology (p + q))
    (hcap : Function.Surjective (fun c => AlgebraicTopology.Products.CapBoundary.capHomology K p q c z)) :
    FiniteDimensional k ((AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).homology q) := by
  obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K) (p + q) z
  obtain ⟨S, hS, hSz⟩ := exists_finite_cap_container K p q z.val
  let : Module.Finite k S := Module.Finite.of_fg hS
  let f : S →ₗ[k] (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).homology q :=
    (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K) q).comp
      ((cycleRetraction (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K) q).comp S.subtype)
  apply Module.Finite.of_surjective f
  intro a
  obtain ⟨c, rfl⟩ := hcap a
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of k k)) p c
  refine ⟨⟨AlgebraicTopology.Products.Cap.cap K p q c.val z.val, hSz c.val⟩, ?_⟩
  refine Eq.trans ?_ (AlgebraicTopology.Products.CapBoundary.capHomology_class_class K p q c z).symm
  change AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K) q
    (cycleRetraction (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K) q
      (AlgebraicTopology.Products.CapBoundary.capCycles K p q c z).val) = _
  rw [cycleRetraction_cycle]

end Cap

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

include d

/-- The actual singular rational homology of a compact complex manifold is finite. -/
theorem rational_singularHomology_finite (q : ℕ) :
    FiniteDimensional ℚ (AlgebraicTopology.Singular.Cohomology.Homology ℚ (TopCat.of M) q) := by
  by_cases hq : q ≤ 2 * d
  · let p := 2 * d - q
    have hpq : p + q = 2 * d := Nat.sub_add_cancel hq
    let z := AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) (TopCat.of M) (p + q)
      (AlgebraicTopology.Duality.Poincare.CompactMeaning.complexFundamentalClassInDegree d (M := M) (p + q) hpq)
    apply finite_homology_of_cap_surjective (TopCat.toSSet.obj (TopCat.of M)) p q z
    exact (AlgebraicTopology.Duality.Poincare.Manifold.compactComplexManifoldPoincareDuality d (M := M) p q hpq).toLinearEquiv.surjective
  · let : Subsingleton (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) q) :=
      ModuleCat.subsingleton_of_isZero
        (AlgebraicTopology.Duality.Poincare.Manifold.compactComplexManifold_singularCohomology_isZero d (M := M) q (by omega))
    let : FiniteDimensional ℚ (Module.Dual ℚ
        ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of M)).homology q)) :=
      Module.Finite.of_surjective (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (TopCat.of M) q).toLinearMap
        (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (TopCat.of M) q).surjective
    change FiniteDimensional ℚ ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of M)).homology q)
    exact (Module.finite_dual_iff ℚ).mp inferInstance

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CMCompactManifold.CompactManifoldFiniteness
