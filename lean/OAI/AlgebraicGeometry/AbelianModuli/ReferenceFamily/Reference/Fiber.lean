import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum
import OAI.RepresentationTheory.Theta.Geometric.Torus.Data

/-! # Fiber -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber

noncomputable section

/-! Extract the exact analytic reference fiber supplied by CongruenceLevel,
without any moduli scheme or algebraic comparison input. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} (P : Datum.RankThreePELDatum E s)

abbrev ReferenceTangent (s : ℕ) := Fin (3 * Fintype.card (Fin s)) → ℂ

structure ReferenceAnalyticFiber (z : P.domain) where
  projection : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) →ₗ[ℂ] ReferenceTangent s
  lattice : AddSubgroup (ReferenceTangent s)
  form : ReferenceTangent s →ₗ⋆[ℂ] ReferenceTangent s →ₗ[ℂ] ℂ
  action : NumberField.RingOfIntegers E →+* Module.End ℂ (ReferenceTangent s)
  kernel : projection.ker = P.periodFamily z.val
  surjective : Function.Surjective projection
  embedding_injective : Function.Injective (fun v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E =>
    projection (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings v))
  lattice_membership : ∀ t, t ∈ lattice ↔ ∃ v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, v ∈ P.lattice ∧
    t = projection (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings v)
  discrete : DiscreteTopology lattice
  compact : CompactSpace (ReferenceTangent s ⧸ lattice)
  projective : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.IsProjectiveComplexTorus (ReferenceTangent s) lattice
  hermitian : ∀ u v, form v u = star (form u v)
  positive : ∀ u, u ≠ 0 → 0 < (form u u).re
  polarization : ∀ v w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E,
    (form (projection (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings v))
      (projection (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings w))).im = (P.traceForm v w : ℝ)
  equivariant : ∀ (a : NumberField.RingOfIntegers E) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E),
    action a (projection (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings v)) =
      projection (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings ((a : E) • v))

theorem referenceAnalyticFiber_nonempty (hP : P.IsAdmissible) (z : P.domain) :
    Nonempty (ReferenceAnalyticFiber P z) := by
  rcases hP with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hf⟩
  obtain ⟨π, Γ, H, ρ, hk, hs, hi, hΓ, hd, hc, hp, hh, hpos, hpol, he⟩ := (hf z.val z.property).2
  exact ⟨⟨π, Γ, H, ρ, hk, hs, hi, hΓ, hd, hc, hp, hh, hpos, hpol, he⟩⟩

def referenceAnalyticFiber (hP : P.IsAdmissible) (z : P.domain) : ReferenceAnalyticFiber P z :=
  Classical.choice (referenceAnalyticFiber_nonempty P hP z)

variable {P}

def ReferenceAnalyticFiber.periodData {z : P.domain} (F : ReferenceAnalyticFiber P z) :
    RepresentationTheory.Theta.Geometric.Torus.Data.CM.ProjectivePeriodData :=
  letI := F.discrete
  letI := F.compact
  RepresentationTheory.Theta.Geometric.Torus.Data.CM.ProjectivePeriodData.ofCompactProjectiveTorus _ F.lattice F.projective

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber
