import OAI.AlgebraicTopology.Kunneth.ChainSplittingD
import OAI.AlgebraicTopology.Products.CapBoundary
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Cap Finiteness Of -/

namespace OAI.AlgebraicTopology.Kunneth.CapFinitenessOf

noncomputable section

/-! Finite support of a cap-product chain bounds the image of duality. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicTopology.Products.CapBoundary
open scoped Simplicial

namespace Construction.CapFiniteness

variable {k : Type} [Field k]

theorem simplexChain_span (K : SSet.{0}) (n : ℕ) :
    Submodule.span k (Set.range (Cohomology.Singular.ChainDual.simplexChain (R := k) K (n := n))) = ⊤ := by
  let S := Submodule.span k (Set.range (Cohomology.Singular.ChainDual.simplexChain (R := k) K (n := n)))
  have h : S.mkQ = 0 := by
    apply Cohomology.Singular.ChainDual.chainFunctional_ext K (ModuleCat.of k (((Cohomology.Singular.ChainDual.simplicialScalarChains K).X n) ⧸ S))
    intro s
    exact (Submodule.Quotient.mk_eq_zero S).mpr (Submodule.subset_span ⟨s, rfl⟩)
  apply Submodule.eq_top_iff'.mpr
  intro z
  exact (Submodule.Quotient.mk_eq_zero S).mp (LinearMap.congr_fun h z)

/-- Capping with a fixed chain always lands in a finitely generated subspace. -/
theorem exists_finite_cap_container (K : SSet.{0}) (p q : ℕ)
    (z : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X (p + q)) :
    ∃ S : Submodule k ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X q),
      S.FG ∧ ∀ c, Products.Cap.cap K p q c z ∈ S := by
  have hz : z ∈ Submodule.span k (Set.range (Cohomology.Singular.ChainDual.simplexChain (R := k) K (n := p + q))) := by
    rw [simplexChain_span]
    trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    refine ⟨k ∙ Cohomology.Singular.ChainDual.simplexChain (R := k) K (Products.SimplexFaceIdentities.backFace K p q s),
      Submodule.fg_span_singleton _, ?_⟩
    intro c
    rw [Products.Cap.cap_simplex]
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

/-- If capping with one homology class is surjective, its target homology
 is finite-dimensional. This uses a finite representative of that class. -/
theorem finite_homology_of_cap_surjective (K : SSet.{0}) (p q : ℕ)
    (z : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).homology (p + q))
    (hcap : Function.Surjective (fun c => Products.CapBoundary.capHomology K p q c z)) :
    FiniteDimensional k ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).homology q) := by
  obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K) (p + q) z
  obtain ⟨S, hS, hSz⟩ := exists_finite_cap_container K p q z.val
  let : Module.Finite k S := Module.Finite.of_fg hS
  let f : S →ₗ[k] (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).homology q :=
    (Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K) q).comp
      ((ChainSplittingD.Construction.ChainSplitting.cycleRetraction (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K) q).comp S.subtype)
  apply Module.Finite.of_surjective f
  intro a
  obtain ⟨c, rfl⟩ := hcap a
  obtain ⟨c, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of k k)) p c
  refine ⟨⟨Products.Cap.cap K p q c.val z.val, hSz c.val⟩, ?_⟩
  refine Eq.trans ?_ (Products.CapBoundary.capHomology_class_class K p q c z).symm
  change Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K) q
    (ChainSplittingD.Construction.ChainSplitting.cycleRetraction (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K) q
      (Products.CapBoundary.capCycles K p q c z).val) = _
  rw [ChainSplittingD.Construction.ChainSplitting.cycleRetraction_cycle]

end Construction.CapFiniteness

end

end OAI.AlgebraicTopology.Kunneth.CapFinitenessOf
