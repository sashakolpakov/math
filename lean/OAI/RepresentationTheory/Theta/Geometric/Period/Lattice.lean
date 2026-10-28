import OAI.RepresentationTheory.Theta.Geometric.Period.CMComparison
import OAI.RepresentationTheory.Theta.Geometric.Torus.Transport

/-! # Lattice -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The varying period lattice is the literal image of the one fixed
reference lattice under the explicit holomorphic quotient maps. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def Data.ActiveHeckeThetaData.periodReferenceEmbedding (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) :
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E →+ Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s) where
  toFun v := D.periodProjection z (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings v)
  map_zero' := by
    have hz : Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings (0 : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) = 0 := by
      ext i <;> simp [Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates]
    rw [hz, map_zero]
  map_add' v w := by
    have ha : Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings (v + w) =
        Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings v +
          Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings w := by
      ext i <;> simp [Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates]
    rw [ha, map_add]

def Data.ActiveHeckeThetaData.periodLattice (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) : AddSubgroup (Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :=
  D.pel.reference.lattice.toAddSubgroup.map (D.periodReferenceEmbedding z)

theorem Data.ActiveHeckeThetaData.periodLattice_mem (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (t : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :
    t ∈ D.periodLattice z ↔ ∃ v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, v ∈ D.pel.reference.lattice ∧
      D.periodReferenceEmbedding z v = t := Iff.rfl

theorem Data.ActiveHeckeThetaData.periodReferenceEmbedding_differentiable (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Differentiable ℂ (fun z => D.periodReferenceEmbedding z v) :=
  D.periodProjection_differentiable.comp (differentiable_id.prodMk (differentiable_const _))

section

variable {x : D.domain} (F : D.ReferenceAnalyticFiber x)

theorem Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.periodComparison_mem (hg : D.pel.HasIntegralModelGeometry)
    (t : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :
    F.periodComparison D hg t ∈ F.lattice ↔ t ∈ D.periodLattice x.val := by
  rw [F.lattice_membership, D.periodLattice_mem]
  apply exists_congr
  intro v
  apply and_congr_right
  intro _
  rw [← F.periodComparison_projection D hg]
  exact ⟨fun h => ((F.periodComparison D hg).injective h).symm,
    fun h => congrArg (F.periodComparison D hg) h.symm⟩

theorem Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.transportedLattice_eq (hg : D.pel.HasIntegralModelGeometry) :
    (F.periodData D).transportedLattice (F.periodComparison D hg).toContinuousLinearEquiv =
      (D.periodLattice x.val).toIntSubmodule := by
  ext t
  exact F.periodComparison_mem D hg t

include F in
theorem Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.periodReferenceEmbedding_injective (hg : D.pel.HasIntegralModelGeometry) :
    Function.Injective (D.periodReferenceEmbedding x.val) := by
  intro v w h
  apply F.embedding_injective
  have he := congrArg (F.periodComparison D hg) h
  exact (F.periodComparison_projection D hg _).symm.trans
    (he.trans (F.periodComparison_projection D hg _))

end

theorem Data.ActiveHeckeThetaData.periodLattice_geometry (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    DiscreteTopology (D.periodLattice x.val) ∧
      CompactSpace (Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s) ⧸ D.periodLattice x.val) ∧
      NumberTheory.ArithmeticGroups.Data.CongruenceLevel.IsProjectiveComplexTorus (Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) (D.periodLattice x.val) := by
  let F := D.referenceAnalyticFiber hg x
  let G := (F.periodData D).transport (F.periodComparison D hg).toContinuousLinearEquiv
  have hL : G.periodIntegerLattice = (D.periodLattice x.val).toIntSubmodule :=
    F.transportedLattice_eq D hg
  refine ⟨?_, ?_, ?_⟩
  · have h : DiscreteTopology G.periodIntegerLattice := inferInstance
    rw [hL] at h
    exact h
  · have h : CompactSpace G.periodTorus := inferInstance
    change CompactSpace (Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s) ⧸ G.periodIntegerLattice.toAddSubgroup) at h
    rw [hL] at h
    exact h
  · have h := G.projective
    change NumberTheory.ArithmeticGroups.Data.CongruenceLevel.IsProjectiveComplexTorus (Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s))
      G.periodIntegerLattice.toAddSubgroup at h
    rw [hL] at h
    exact h

def Data.ActiveHeckeThetaData.canonicalPeriodData (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    Torus.Data.CM.ProjectivePeriodData := by
  have h := D.periodLattice_geometry hg x
  let := h.1
  let := h.2.1
  exact Torus.Data.CM.ProjectivePeriodData.ofCompactProjectiveTorus _
    (D.periodLattice x.val) h.2.2

end

end OAI.RepresentationTheory.Theta.Geometric
