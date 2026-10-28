import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ComponentUniformization
import OAI.NumberTheory.ArithmeticGroups.Diagonal

/-! # Reference Cover -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceCover.CM

noncomputable section

/-! Identify the actual ReferenceFamily principal uniformization with the source's
ball domain and principal orbit relation. Only the open-set presentation
changes; the covering map is transported along equality of those domains. -/

open scoped Classical _root_.Manifold
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

def CoverProperty (U : TopologicalSpace.Opens GeometricSource.CM.BallChart)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : U → X.analyticSpace) : Prop :=
  Function.Surjective π ∧ IsCoveringMap π ∧
  MDifferentiable 𝓘(ℂ, GeometricSource.CM.BallChart) 𝓘(ℂ, X.analyticModel) π ∧
  ∀ z, Function.Bijective (mfderiv 𝓘(ℂ, GeometricSource.CM.BallChart) 𝓘(ℂ, X.analyticModel) π z)

def transportPoint {U V : TopologicalSpace.Opens GeometricSource.CM.BallChart} (h : U = V) (z : U) : V :=
  ⟨z.val, h ▸ z.property⟩

theorem transport_cover {U V : TopologicalSpace.Opens GeometricSource.CM.BallChart} (h : U = V)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : V → X.analyticSpace)
    (hπ : CoverProperty V X π) :
    CoverProperty U X (π ∘ transportPoint h) := by
  subst V
  exact hπ

variable (E : IntermediateField ℚ ℂ) [NumberField E]
  [IsGalois ℚ E] [NumberField.IsCMField E]
  (B : GeometricSource.CM.BallDatum E) {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

omit [IsGalois ℚ E] in
theorem reference_domain_eq (hb : P.b = B.b) (hμ : P.μ = E.val.toRingHom) :
    P.domain = B.domain := by
  ext z
  change (Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings (Matrix.diagonal ![1, 1, P.b])
      P.distinguished (Geometry.ComplexBall.PrescribedSignsB.lineVector z)
        (star (Geometry.ComplexBall.PrescribedSignsB.lineVector z))).re < 0 ↔ _
  rw [NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.localB_diagonal_real]
  have hc : (P.embeddings P.distinguished P.b).re = (B.b : ℂ).re := by
    change (P.μ P.b).re = _
    rw [hμ, hb]
    rfl
  have hz0 : Geometry.ComplexBall.PrescribedSignsB.lineVector z 0 = z 0 := rfl
  have hz1 : Geometry.ComplexBall.PrescribedSignsB.lineVector z 1 = z 1 := rfl
  have hz2 : Geometry.ComplexBall.PrescribedSignsB.lineVector z 2 = (1 : ℂ) := rfl
  simp only [hc, hz0, hz1, hz2, Complex.normSq_one, mul_one,
    GeometricSource.CM.BallDatum.domain, Set.mem_ofPred_eq]
  constructor <;> intro hz <;> linarith

omit [IsGalois ℚ E] in
theorem reference_domainOpen_eq (hb : P.b = B.b) (hμ : P.μ = E.val.toRingHom) :
    B.domainOpen = P.domainOpen := by
  apply SetLike.coe_injective
  exact (reference_domain_eq E B P hb hμ).symm

omit [IsGalois ℚ E] [NumberField E] [NumberField.IsCMField E] in
theorem reference_lineAction_eq (hμ : P.μ = E.val.toRingHom)
    (g : GeometricSource.CM.Vec E ≃ₗ[E] GeometricSource.CM.Vec E) (z : GeometricSource.CM.BallChart) : P.lineAction g z = GeometricSource.CM.BallDatum.lineAction (E := E) g z := by
  unfold AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.lineAction GeometricSource.CM.BallDatum.lineAction
  rw [hμ]
  rfl

omit [IsGalois ℚ E] in
/-- The ReferenceFamily principal component has precisely the concrete source-cover
predicate when its Hermitian coefficient, embedding and lattice agree. -/
theorem reference_cover_as_source
    (hb : P.b = B.b) (hμ : P.μ = E.val.toRingHom) (hΛ : P.lattice = B.lattice)
    (N : ℕ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (hdim : X.complexDimension = 2)
    (Γ : Subgroup (GeometricSource.CM.Vec E ≃ₗ[E] GeometricSource.CM.Vec E))
    (hΓ : ∀ g, g ∈ Γ ↔
      (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel P.b P.lattice N g ∧
        LinearMap.det g.toLinearMap = 1))
    (hcover : P.IsUniformizedBy X Γ) :
    ∃ π : B.Domain → X.analyticSpace, B.IsBallCover N X π := by
  obtain ⟨ρ, hρ, horbits⟩ := hcover
  let h := reference_domainOpen_eq E B P hb hμ
  let π := ρ ∘ transportPoint h
  have hp : CoverProperty B.domainOpen X π := transport_cover h X ρ hρ
  refine ⟨π, hdim, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, ?_⟩
  intro z w
  change ρ (transportPoint h z) = ρ (transportPoint h w) ↔ _
  rw [horbits]
  unfold AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.OrbitRelation
  simp only [transportPoint, reference_lineAction_eq E P hμ]
  apply exists_congr
  intro g
  rw [hΓ, hb, hΛ, ← ReferenceDatum.CM.principalLevel_iff E B N g]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceCover.CM
