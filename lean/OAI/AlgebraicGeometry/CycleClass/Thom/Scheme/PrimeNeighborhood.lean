import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.UniformizerSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity

/-! # Prime Neighborhood -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PrimeNeighborhood.Constructions

noncomputable section

/-! Algebraic neighborhoods on which a prime divisor is regular and its
actual uniformizer has precisely the original analytic zero set. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.UniformizerSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left]
  (z : {x : X.left // Order.coheight x = 1})

local notation "Z" => OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport X z

theorem section_uniformizer_primeSupport_neighborhood (U : X.left.Opens) (hU : IsAffineOpen U)
    (hzU : z.val ∈ U) (p : Γ(X.left, U)) (hp : Irreducible (X.left.presheaf.germ U z.val hzU p)) :
    ∃ b : Γ(X.left, U), IsUnit (X.left.presheaf.germ U z.val hzU b) ∧
      ∀ y : SectionEvaluation.Constructions.analyticOpen X U, SectionEvaluation.Constructions.sectionEvaluationOn X U b y ≠ 0 →
        (SectionEvaluation.Constructions.sectionEvaluationOn X U p y = 0 ↔ y.val ∈ Set.range (RegularSupport.Constructions.supportInclusion X Z)) := by
  obtain ⟨b, hb, hs⟩ := UniformizerSupport.Constructions.smooth_uniformizer_analytic_support_neighborhood X U hU z.val hzU z.property p hp
  refine ⟨b, hb, ?_⟩
  intro y hy
  rw [RegularSupport.Constructions.supportInclusion_range]
  exact hs y hy

omit [IsIntegral X.left] [AlgebraicGeometry.IsNoetherian X.left] in
theorem exists_prime_regular_neighborhood (U : X.left.Opens) (hU : IsAffineOpen U) (hzU : z.val ∈ U)
    (b : Γ(X.left, U)) (hb : IsUnit (X.left.presheaf.germ U z.val hzU b)) :
    ∃ W : X.left.Opens, z.val ∈ W ∧ ∃ hWU : W ≤ U,
      ∀ y : SectionEvaluation.Constructions.analyticOpen X W, y.val ∈ RegularSupport.Constructions.regularAmbientOpen X Z ∧
        SectionEvaluation.Constructions.sectionEvaluationOn X U b ⟨y.val, hWU y.property⟩ ≠ 0 := by
  let R : X.left.Opens :=
    ⟨(Geometric.StratumDimension.supportSingularBoundary Z X.hom)ᶜ, (Geometric.StratumDimension.isClosed_supportSingularBoundary Z X.hom).isOpen_compl⟩
  have hzR : z.val ∈ R := by
    have h := Geometric.StratumDimension.genericPoint_not_mem_supportSingularBoundary Z X.hom
    have he : irreducibleSetEquivPoints Z = z.val := irreducibleSetEquivPoints.apply_symm_apply z.val
    rwa [he] at h
  let W := X.left.basicOpen b ⊓ R
  have hWU : W ≤ U := inf_le_left.trans (X.left.basicOpen_le b)
  refine ⟨W, ⟨(X.left.mem_basicOpen b z.val hzU).mpr hb, hzR⟩, hWU, ?_⟩
  intro y
  refine ⟨y.property.2, ?_⟩
  intro hy
  have hn := (UniformizerSupport.Constructions.sectionEvaluationOn_zero_iff_nonunit X U hU b ⟨y.val, hWU y.property⟩).mp hy
  exact hn ((X.left.mem_basicOpen b (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y.val) (hWU y.property)).mp y.property.1)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PrimeNeighborhood.Constructions
