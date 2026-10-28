import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrimeDivisibleDifferenceComponent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ComponentConstantFiniteImage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ImageHomRigidity

/-! # Prime Divisible Difference Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Geometric separation: an actual polarized automorphism difference divisible by every power of an integer at least two vanishes over an algebraically closed field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem Moduli.Isomorphisms.LevelPreservingIso.difference_zero_of_allPowers (e : Moduli.Isomorphisms.LevelPreservingIso A A)
    (q : ℕ) (hq : 2 ≤ q)
    (hdiv : ∀ k : ℕ, ∃ d : A.abelian.EndRing, (q ^ k) • d = e.endRingUnit.val - 1) :
    e.endRingUnit.val - 1 = 0 := by
  have : CompactSpace A.abelian.scheme.left :=
    (quasiCompact_iff_compactSpace A.abelian.scheme.hom).mp inferInstance
  have : IsNoetherian A.abelian.scheme.left := { __ := LocallyOfFiniteType.isLocallyNoetherian A.abelian.scheme.hom }
  obtain ⟨E⟩ := A.graphBundle_isAmple_overAlgClosed.exists_powerProjectiveEmbedding A.abelian.scheme.hom
  let f := (e.abelian.hom * (𝟙 A.abelian.scheme)⁻¹).left
  have hfinite : (Set.range f).Finite := by
    apply ComponentConstantFiniteImage.finite_range_of_constant_reduced_components A.abelian.scheme.hom f
    intro C hC
    let Z : TopologicalSpace.Closeds A.abelian.scheme.left := ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩
    let Y := ReducedClosedSubschemes.reducedClosedSubscheme A.abelian.scheme.left Z
    let i := ReducedClosedSubschemes.reducedClosedInclusion A.abelian.scheme.left Z
    have : IsClosedImmersion i := ReducedClosedSubschemes.reducedClosedInclusion_isClosedImmersion _ Z
    have : IsReduced Y := ReducedClosedSubschemes.reducedClosedSubscheme_isReduced _ Z
    have : IrreducibleSpace Y := ReducedComponentFiniteness.reducedClosedSubscheme_irreducible _ Z hC.1
    have : IsIntegral Y := isIntegral_of_irreducibleSpace_of_isReduced Y
    have : IsProper (i ≫ A.abelian.scheme.hom) := inferInstance
    exact e.difference_constant_of_allPowers A E i q hq hdiv
  apply A.abelian.endRing_eq_zero_of_finite_range (e.endRingUnit.val - 1)
  exact (congrArg (fun a : A.abelian.scheme ⟶ A.abelian.scheme => (Set.range a.left).Finite)
    e.endRing_difference_hom).mpr hfinite

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
