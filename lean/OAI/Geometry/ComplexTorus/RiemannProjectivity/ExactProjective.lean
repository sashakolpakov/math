import OAI.Geometry.ComplexTorus.RiemannProjectivity.AlgebraicPeriod
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs

/-! # Exact Projective -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.ExactProjective.Constructions.ExactProjectiveClosure

noncomputable section

/-! # RiemannProjectivity: the algebraic projective closure has exactly the original complex points -/

open Set _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure

variable {n : ℕ}

theorem homogeneous_mem_underlying (p : Projectivization ℂ (Fin (n + 1) → ℂ))
    (q : MvPolynomial (Fin (n + 1)) ℂ) {d : ℕ} (hq : q.IsHomogeneous d) :
    q ∈ (ProjectiveClosureIs.Constructions.ProjectiveClosure.underlyingPoint p).asHomogeneousIdeal ↔ MvPolynomial.eval p.rep q = 0 := by
  have heq := congrArg (ProjectiveClosureIs.Constructions.ProjectiveClosure.underlyingPoint (n := n)) p.mk_rep
  rw [← heq]
  exact AlgebraicGeometry.Foundations.Scheme.ProjectiveVectorScale.projectiveVectorPoint_homogeneous_mem_iff p.rep p.rep_nonzero q d hq (IsLocalRing.closedPoint ℂ)

theorem underlying_mem_support_iff {S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))}
    (Q : Finset (MvPolynomial (Fin (n + 1)) ℂ)) (hQ : ∀ q ∈ Q, ∃ d, q.IsHomogeneous d)
    (hS : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone S = {v | ∀ q ∈ Q, MvPolynomial.eval v q = 0})
    (p : Projectivization ℂ (Fin (n + 1) → ℂ)) : ProjectiveClosureIs.Constructions.ProjectiveClosure.underlyingPoint p ∈ ProjectiveClosureIs.Constructions.ProjectiveClosure.closureSupport S ↔ p ∈ S := by
  let Z : Set (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) := ProjectiveSpectrum.zeroLocus (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (Q : Set _)
  have hZ : IsClosed Z := ProjectiveSpectrum.isClosed_zeroLocus _ _
  have hsub : ProjectiveClosureIs.Constructions.ProjectiveClosure.underlyingPoint '' S ⊆ Z := by
    rintro _ ⟨a, ha, rfl⟩
    intro q hq
    obtain ⟨d, hd⟩ := hQ q hq
    apply (homogeneous_mem_underlying a q hd).mpr
    have hcone : a.rep ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone S := by
      rw [AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.mem_projectiveCone_iff S a.rep a.rep_nonzero, a.mk_rep]
      exact ha
    rw [hS] at hcone
    exact hcone q hq
  have hclosure : (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureSupport S : Set (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) ⊆ Z := closure_minimal hsub hZ
  constructor
  · intro hp
    have hpZ := hclosure hp
    have hrep : p.rep ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone S := by
      rw [hS]
      intro q hq
      obtain ⟨d, hd⟩ := hQ q hq
      exact (homogeneous_mem_underlying p q hd).mp (hpZ hq)
    rwa [AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.mem_projectiveCone_iff S p.rep p.rep_nonzero, p.mk_rep] at hrep
  · exact ProjectiveClosureIs.Constructions.ProjectiveClosure.underlying_mem_support S

theorem liftedMap_surjective {T : Type} [TopologicalSpace T]
    (f : T → Projectivization ℂ (Fin (n + 1) → ℂ))
    (Q : Finset (MvPolynomial (Fin (n + 1)) ℂ)) (hQ : ∀ q ∈ Q, ∃ d, q.IsHomogeneous d)
    (hS : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) = {v | ∀ q ∈ Q, MvPolynomial.eval v q = 0}) :
    Function.Surjective (ProjectiveClosureIs.Constructions.ProjectiveClosure.liftedMap f) := by
  let S := range f
  let j := ProjectiveClosureIs.Constructions.ProjectiveClosure.inclusionOver S
  let : IsClosedImmersion j.left := inferInstanceAs (IsClosedImmersion (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureInclusion S))
  intro q
  let p := (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j q)
  have hp : AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n p = AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j q :=
    (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).apply_symm_apply _
  have hpoint : ProjectiveClosureIs.Constructions.ProjectiveClosure.underlyingPoint p = ProjectiveClosureIs.Constructions.ProjectiveClosure.closureInclusion S (q.left (IsLocalRing.closedPoint ℂ)) :=
    congrArg (fun r : AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n => r.left (IsLocalRing.closedPoint ℂ)) hp
  have hpS : p ∈ S := (underlying_mem_support_iff Q hQ hS p).mp (by
    rw [hpoint]
    exact (ProjectiveClosureIs.Constructions.ProjectiveClosure.inclusion_range S).subset ⟨q.left (IsLocalRing.closedPoint ℂ), rfl⟩)
  obtain ⟨t, ht⟩ := hpS
  refine ⟨t, ?_⟩
  apply (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion j).injective
  rw [ProjectiveClosureIs.Constructions.ProjectiveClosure.liftedMap_inclusion, ht]
  exact hp

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.ExactProjective.Constructions.ExactProjectiveClosure
