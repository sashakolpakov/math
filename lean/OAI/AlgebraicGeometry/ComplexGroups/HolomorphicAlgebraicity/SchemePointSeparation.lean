import OAI.AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints
import OAI.AlgebraicGeometry.Foundations.Scheme.ImmersionComplexPoints
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointUnderlying
import OAI.AlgebraicGeometry.CycleClass.Geometric.ReducedClosed

/-! # Scheme Point Separation -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SchemePointSeparation.Constructions.Algebraization

noncomputable section

/-!
# Algebraic closed subsets from regular-function separators

Regular functions on affine open charts give Zariski open separators of
complex points. Such separators identify exactly the complex points of the
reduced closed subscheme supported on their Zariski closure.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set

theorem underlying_mem_basicOpen_iff
    (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (r : Γ(X.left, ⊤)) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p ∈ X.left.basicOpen r ↔ Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X p r ≠ 0 := by
  rw [← X.left.map_PrimeSpectrum_basicOpen_of_affine r]
  change X.left.isoSpec.hom (p.left ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.basePoint) ∈ PrimeSpectrum.basicOpen r ↔ _
  have heq := congrArg (fun f : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec Γ(X.left, ⊤) =>
    f ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.basePoint) (Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv_spec X p)
  rw [Scheme.Hom.comp_apply] at heq
  change ¬ r ∈ (X.left.isoSpec.hom (p.left ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.basePoint)).asIdeal ↔ _
  rw [← heq]
  change ¬ (Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X p r) ∈ (⊥ : Ideal ℂ) ↔ _
  simp only [Ideal.mem_bot]

theorem exists_open_separator_of_affine_regular_function
    {X T : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine T.left]
    (i : T ⟶ X) [IsOpenImmersion i.left]
    {S : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)} (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints T)
    (r : Γ(T.left, ⊤)) (hr : Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv T p r ≠ 0)
    (hzero : ∀ q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints T, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i q ∈ S →
      Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv T q r = 0) :
    ∃ U : X.left.Opens, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i p) ∈ U ∧
      ∀ q ∈ S, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying q ∉ U := by
  let U : X.left.Opens := ⟨i.left '' (T.left.basicOpen r : Set T.left),
    i.left.isOpenEmbedding.isOpenMap _ (T.left.basicOpen r).isOpen⟩
  refine ⟨U, ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p, (underlying_mem_basicOpen_iff T p r).mpr hr, rfl⟩, ?_⟩
  intro q hq hqU
  obtain ⟨x, hx, hxq⟩ := hqU
  have hqrange : q.left (⊥ : PrimeSpectrum ℂ) ∈ range i.left := ⟨x, hxq⟩
  obtain ⟨q', hq'⟩ := Foundations.Scheme.ImmersionComplexPoints.surjectiveOnStalks_relativeFieldPoint_existsLift i q
    (⊥ : PrimeSpectrum ℂ) hqrange
  have hqx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying q' = x := by
    apply i.left.isOpenEmbedding.injective
    have h := congrArg ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying hq'
    change i.left (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying q') = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying q at h
    exact h.trans hxq.symm
  have hnonzero : Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv T q' r ≠ 0 :=
    (underlying_mem_basicOpen_iff T q' r).mp (hqx.symm ▸ hx)
  exact hnonzero (hzero q' (by change (q' ≫ i) ∈ S; rwa [hq']))

theorem exists_reduced_closed_subscheme_of_open_separators
    (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (S : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (hsep : ∀ p ∉ S, ∃ U : X.left.Opens, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p ∈ U ∧
      ∀ q ∈ S, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying q ∉ U) :
    ∃ (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (i : Z ⟶ X),
      IsReduced Z.left ∧ IsClosedImmersion i.left ∧ range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) = S := by
  let C : TopologicalSpace.Closeds X.left :=
    ⟨closure (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying '' S), isClosed_closure⟩
  have hC (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p ∈ C ↔ p ∈ S := by
    constructor
    · intro hp
      by_contra hpS
      obtain ⟨U, hpU, hU⟩ := hsep p hpS
      have hclosure : closure (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying '' S) ⊆ (U : Set X.left)ᶜ := by
        apply closure_minimal _ U.isOpen.isClosed_compl
        rintro _ ⟨q, hq, rfl⟩
        exact hU q hq
      exact hclosure hp hpU
    · intro hp
      exact subset_closure ⟨p, hp, rfl⟩
  let Z := Over.mk (CycleClass.Geometric.ReducedClosed.reducedClosedι C ≫ X.hom)
  let i : Z ⟶ X := Over.homMk (CycleClass.Geometric.ReducedClosed.reducedClosedι C) rfl
  have hi : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion (CycleClass.Geometric.ReducedClosed.reducedClosedι C))
  refine ⟨Z, i, inferInstanceAs (IsReduced (CycleClass.Geometric.ReducedClosed.reducedClosedScheme C)), hi, ?_⟩
  change range (fun q => q ≫ i) = S
  rw [Foundations.Scheme.ImmersionComplexPoints.range_closedImmersion_complexPointMap i]
  ext p
  change p.left (⊥ : PrimeSpectrum ℂ) ∈ range (CycleClass.Geometric.ReducedClosed.reducedClosedι C) ↔ p ∈ S
  rw [CycleClass.Geometric.ReducedClosed.range_reducedClosedι]
  exact hC p

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SchemePointSeparation.Constructions.Algebraization
