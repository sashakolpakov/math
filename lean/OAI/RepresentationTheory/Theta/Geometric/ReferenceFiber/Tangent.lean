import OAI.RepresentationTheory.Theta.Geometric.Reference.Domain
import OAI.RepresentationTheory.Theta.Geometric.Torus.Data

/-! # Tangent -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Witnesses for the reference analytic fiber, retaining its literal
lattice, trace polarization, and integral CM action. This record merely
packages the analytic-fiber clause already present in the PEL input. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

abbrev Data.ActiveHeckeThetaData.referenceTangent := Fin (3 * Fintype.card (Fin s)) → ℂ

structure Data.ActiveHeckeThetaData.ReferenceAnalyticFiber (x : D.domain) where
  projection : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) →ₗ[ℂ] Data.ActiveHeckeThetaData.referenceTangent (s := s)
  lattice : AddSubgroup (Data.ActiveHeckeThetaData.referenceTangent (s := s))
  form : Data.ActiveHeckeThetaData.referenceTangent (s := s) →ₗ⋆[ℂ] Data.ActiveHeckeThetaData.referenceTangent (s := s) →ₗ[ℂ] ℂ
  action : NumberField.RingOfIntegers E →+* Module.End ℂ (Data.ActiveHeckeThetaData.referenceTangent (s := s))
  kernel : projection.ker = D.pel.reference.periodFamily x.val
  surjective : Function.Surjective projection
  embedding_injective : Function.Injective (fun v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E =>
    projection (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings v))
  lattice_membership : ∀ t, t ∈ lattice ↔ ∃ v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, v ∈ D.pel.reference.lattice ∧
    t = projection (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings v)
  discrete : DiscreteTopology lattice
  compact : CompactSpace (Data.ActiveHeckeThetaData.referenceTangent (s := s) ⧸ lattice)
  projective : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.IsProjectiveComplexTorus (Data.ActiveHeckeThetaData.referenceTangent (s := s)) lattice
  hermitian : ∀ u v, form v u = star (form u v)
  positive : ∀ u, u ≠ 0 → 0 < (form u u).re
  polarization : ∀ v w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E,
    (form (projection (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings v))
      (projection (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings w))).im =
        (D.pel.reference.traceForm v w : ℝ)
  equivariant : ∀ (a : NumberField.RingOfIntegers E) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E),
    action a (projection (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings v)) =
      projection (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings ((a : E) • v))

theorem Data.ActiveHeckeThetaData.referenceAnalyticFiber_nonempty (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    Nonempty (D.ReferenceAnalyticFiber x) := by
  have h := D.reference_analytic_fiber hg x
  simp only [NumberTheory.ArithmeticGroups.Data.CongruenceLevel.AnalyticPolarizedFiber] at h
  obtain ⟨p, L, H, a, hk, hs, hi, hL, hd, hc, hp, hh, hpos, hpol, he⟩ := h
  exact ⟨⟨p, L, H, a, hk, hs, hi, hL, hd, hc, hp, hh, hpos, hpol, he⟩⟩

def Data.ActiveHeckeThetaData.referenceAnalyticFiber (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) : D.ReferenceAnalyticFiber x :=
  Classical.choice (D.referenceAnalyticFiber_nonempty hg x)

def Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.periodData {x : D.domain} (F : D.ReferenceAnalyticFiber x) :
    Torus.Data.CM.ProjectivePeriodData :=
  letI := F.discrete
  letI := F.compact
  Torus.Data.CM.ProjectivePeriodData.ofCompactProjectiveTorus _ F.lattice F.projective

end

end OAI.RepresentationTheory.Theta.Geometric
