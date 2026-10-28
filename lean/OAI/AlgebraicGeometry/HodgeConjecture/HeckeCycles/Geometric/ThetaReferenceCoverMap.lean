import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaLinearPrincipal
import OAI.RepresentationTheory.Theta.Geometric.Geometry
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceCover
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverDerivative
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverSmooth

/-! # Theta Reference Cover Map -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaReferenceCoverMap.CM

noncomputable section

/-! The exact principal-level inclusion constructs a holomorphic
surjective map from the actual reference component to the GeometricTheta component. -/

open scoped Classical _root_.NumberField _root_.Manifold ContDiff
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.RepresentationTheory.Theta.Geometric.Geometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceCover.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverFactor.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
  (B : GeometricSource.CM.BallDatum E) (hb : D.pel.reference.b = B.b) (hμ : D.pel.reference.μ = E.val.toRingHom)

include hb hμ in
theorem domain_eq : B.domainOpen = D.domain := by
  apply SetLike.coe_injective
  change B.domain = (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (D.pel.reference.μ D.pel.reference.b) : Set GeometricSource.CM.BallChart)
  rw [hμ, hb]
  rfl

def transported {X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (cover : D.domain → X.analyticSpace) :
    B.Domain → X.analyticSpace :=
  cover ∘ ReferenceCover.CM.transportPoint (domain_eq E D B hb hμ)

include hb hμ in
theorem principal_orbit (hΛ : D.pel.reference.lattice = B.lattice)
    (hc : D.HasFiniteCoordinates) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (cover : D.domain → X.analyticSpace) (hcover : D.IsPeriodUniformization X cover)
    (g : GeometricSource.CM.Vec E ≃ₗ[E] GeometricSource.CM.Vec E) (hg : B.principalLevel D.pel.level g)
    (z w : B.Domain) (hw : w.val = GeometricSource.CM.BallDatum.lineAction g z.val) :
    transported E D B hb hμ cover z = transported E D B hb hμ cover w := by
  have hu : ∀ x y, GeometricSource.CM.hermitian E D.pel.reference.b (g x) (g y) = GeometricSource.CM.hermitian E D.pel.reference.b x y :=
    Eq.mpr (congrArg (fun b : E => ∀ x y, GeometricSource.CM.hermitian E b (g x) (g y) = GeometricSource.CM.hermitian E b x y) hb) hg.1
  have hL : ∀ x, x ∈ D.pel.reference.lattice ↔ g x ∈ D.pel.reference.lattice := by
    simpa only [hΛ] using hg.2.2.1
  have hN : ∀ x ∈ D.pel.reference.lattice, ∃ y ∈ D.pel.reference.lattice,
      g x - x = D.pel.level • y := by
    simpa only [hΛ, natCast_zsmul] using hg.2.2.2
  let γ := LinearUnitaryRepresentative.CM.rational E D.pel.reference.b g hu hg.2.1
  apply (hcover.2.2.2.2 (ReferenceCover.CM.transportPoint (domain_eq E D B hb hμ) z)
    (ReferenceCover.CM.transportPoint (domain_eq E D B hb hμ) w)).mpr
  exact ⟨γ, ThetaLinearPrincipal.CM.member E D g hu hg.2.1 hc hL hN,
    hw.trans (ThetaLinearPrincipal.CM.period E D g hu hg.2.1 hμ
      (ReferenceCover.CM.transportPoint (domain_eq E D B hb hμ) z)).symm⟩

include hb hμ in
theorem exists_map (hΛ : D.pel.reference.lattice = B.lattice)
    (hc : D.HasFiniteCoordinates) (X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (cover : D.domain → X.analyticSpace) (hcover : D.IsPeriodUniformization X cover)
    (π : B.Domain → Y.analyticSpace) (hπ : B.IsBallCover D.pel.level Y π) :
    ReferenceCover.CM.CoverProperty B.domainOpen X (transported E D B hb hμ cover) ∧
    ∃ f : C(Y.analyticSpace, X.analyticSpace),
      ContMDiff 𝓘(ℂ, Y.analyticModel) 𝓘(ℂ, X.analyticModel) ∞ f ∧
      Function.Surjective f ∧ ∀ z, f (π z) = transported E D B hb hμ cover z := by
  let ρ := transported E D B hb hμ cover
  have hρ : ReferenceCover.CM.CoverProperty B.domainOpen X ρ := ReferenceCover.CM.transport_cover (domain_eq E D B hb hμ) X cover
    ⟨hcover.1, hcover.2.1, hcover.2.2.1, hcover.2.2.2.1⟩
  have hfibers : ∀ z w, π z = π w → ρ z = ρ w := by
    intro z w he
    obtain ⟨g, hg, hw⟩ := (hπ.2.2.2.2.2 z w).mp he
    exact principal_orbit E D B hb hμ hΛ hc X cover hcover g hg z w hw
  let f : C(Y.analyticSpace, X.analyticSpace) :=
    ⟨CoverFactor.CM.factor π ρ hπ.2.1, CoverFactor.CM.factor_continuous π ρ hπ.2.1 hπ.2.2.1 hρ.2.1.continuous hfibers⟩
  have hcomp := CoverFactor.CM.factor_comp π ρ hπ.2.1 hfibers
  have hhol := CoverDerivative.CM.descended_map_mdifferentiable π ρ hπ.2.1 hπ.2.2.1
    hπ.2.2.2.1 hπ.2.2.2.2.1 hρ.2.2.1 f hcomp
  exact ⟨hρ, f, (CoverSmooth.CM.quotient_map_contMDiff B D.pel.level Y X π hπ f hhol).1,
    CoverFactor.CM.factor_surjective π ρ hπ.2.1 hρ.1 hfibers, hcomp⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaReferenceCoverMap.CM
