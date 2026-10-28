import OAI.AlgebraicGeometry.CycleClass.Geometric.SmallChainImage
import OAI.AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact

/-! # Relative Chain Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeChainSupport.Cycles

noncomputable section

/-!
# Geometric support and vanishing in relative singular chains

An ordinary singular chain vanishes relative to a subspace exactly when every
simplex with a nonzero coefficient has its entire geometric image there. The
proof identifies the actual subspace-chain image in the canonical finite
coefficient description, then uses the exact relative-chain sequence.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial

variable (X : TopCat.{0}) (A : Set X) (n : ℕ)

/-- Subspace inclusion extends the actual finite coefficients along the
injective map of genuine singular simplices. -/
theorem subspaceChainInclusion_coefficients
    (c : (LocalHomology.Cycles.integralSingularChains (TopCat.of A)).X n) :
    SingularChainSupport.Cycles.singularChainCoefficients X n ((LocalHomology.Cycles.subspaceChainInclusion X A).f n c) =
      Finsupp.mapDomain ((TopCat.toSSet.map (LocalHomology.Cycles.subspaceInclusion X A)).app (.op ⦋n⦌))
        (SingularChainSupport.Cycles.singularChainCoefficients (TopCat.of A) n c) :=
  SmallChainImage.Cycles.simplicialIntegralChainCoefficients_map
    (TopCat.toSSet.map (LocalHomology.Cycles.subspaceInclusion X A)) n c

/-- A finite chain lies in the actual subspace-chain image exactly when
every nonzero simplex has image in that subspace. -/
theorem mem_subspaceChainInclusion_range_iff
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    c ∈ LinearMap.range ((LocalHomology.Cycles.subspaceChainInclusion X A).f n).hom ↔
      ∀ σ, SingularChainSupport.Cycles.singularChainCoefficients X n c σ ≠ 0 →
        Set.range (X.toSSetObjEquiv (.op ⦋n⦌) σ) ⊆ A := by
  constructor
  · rintro ⟨b, rfl⟩ σ hσ
    rw [subspaceChainInclusion_coefficients] at hσ
    obtain ⟨τ, hτ⟩ := Finsupp.mem_range_of_mapDomain_ne_zero hσ
    exact (SmallMayerVietoris.Cycles.mem_subspaceSingularSubcomplex X A (.op ⦋n⦌) σ).1 ⟨τ, hτ⟩
  · intro hc
    let i := (TopCat.toSSet.map (LocalHomology.Cycles.subspaceInclusion X A)).app (.op ⦋n⦌)
    have hi : Function.Injective i := injective_of_mono i
    have hcoeff : SingularChainSupport.Cycles.singularChainCoefficients X n c ∈ Set.range (Finsupp.mapDomain i) := by
      apply (Finsupp.mem_range_mapDomain_iff i hi _).2
      intro σ hσ
      by_contra hn
      apply hσ
      exact (SmallMayerVietoris.Cycles.mem_subspaceSingularSubcomplex X A (.op ⦋n⦌) σ).2 (hc σ hn)
    obtain ⟨b, hb⟩ := hcoeff
    refine ⟨(SingularChainSupport.Cycles.singularChainCoefficients (TopCat.of A) n).symm b, ?_⟩
    apply (SingularChainSupport.Cycles.singularChainCoefficients X n).injective
    rw [subspaceChainInclusion_coefficients]
    exact (congrArg (Finsupp.mapDomain i)
      ((SingularChainSupport.Cycles.singularChainCoefficients (TopCat.of A) n).apply_symm_apply b)).trans hb

/-- The kernel of the actual relative projection is the actual subspace-chain image. -/
theorem relativeChainProjection_ker :
    LinearMap.ker ((LocalHomology.Cycles.relativeChainProjection X A).f n).hom =
      LinearMap.range ((LocalHomology.Cycles.subspaceChainInclusion X A).f n).hom :=
  (LocalHomology.Cycles.relativeChainSequence_degreewiseShortExact X A n).exact.moduleCat_range_eq_ker.symm

/-- Exact geometric support criterion for vanishing in genuine relative chains. -/
theorem relativeChainProjection_eq_zero_iff_supported
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    (LocalHomology.Cycles.relativeChainProjection X A).f n c = 0 ↔
      ∀ σ, LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℤ X n c σ ≠ 0 →
        LocallyFiniteChains.Cycles.singularSimplexImage X n σ ⊆ A := by
  change c ∈ LinearMap.ker ((LocalHomology.Cycles.relativeChainProjection X A).f n).hom ↔ _
  rw [relativeChainProjection_ker]
  exact mem_subspaceChainInclusion_range_iff X A n c

/-- A finite chain whose nonzero simplices lie in the subspace vanishes
under the actual relative-chain projection. -/
theorem relativeChainProjection_eq_zero_of_supported
    (c : (LocalHomology.Cycles.integralSingularChains X).X n)
    (hc : ∀ σ, LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℤ X n c σ ≠ 0 →
      LocallyFiniteChains.Cycles.singularSimplexImage X n σ ⊆ A) :
    (LocalHomology.Cycles.relativeChainProjection X A).f n c = 0 :=
  (relativeChainProjection_eq_zero_iff_supported X A n c).2 hc

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeChainSupport.Cycles
