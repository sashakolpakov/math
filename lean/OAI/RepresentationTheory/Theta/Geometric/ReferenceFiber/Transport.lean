import OAI.RepresentationTheory.Theta.Geometric.Period.Lattice
import OAI.RepresentationTheory.Theta.Geometric.Torus.LinearEquiv
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber

/-! # Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! GeometricTheta's reference fiber is literally the ReferenceFamily fiber at the same
negative line. The fixed quotient coordinates are identified by their
actual lattice-preserving complex-linear map. -/

open scoped _root_.Manifold ContDiff

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def Data.ActiveHeckeThetaData.referenceDomainPoint (x : D.domain) : D.pel.reference.domain :=
  ⟨x.val, by rw [D.reference_domain_eq]; exact x.property⟩

variable {x : D.domain} (F : D.ReferenceAnalyticFiber x)

def Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.toNativeReference : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber D.pel.reference (D.referenceDomainPoint x) where
  projection := F.projection
  lattice := F.lattice
  form := F.form
  action := F.action
  kernel := F.kernel
  surjective := F.surjective
  embedding_injective := F.embedding_injective
  lattice_membership := F.lattice_membership
  discrete := F.discrete
  compact := F.compact
  projective := F.projective
  hermitian := F.hermitian
  positive := F.positive
  polarization := F.polarization
  equivariant := F.equivariant

theorem Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.toNativeReference_periodData : (F.toNativeReference D).periodData = F.periodData D := rfl

def Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.canonicalTorusEquiv (hg : D.pel.HasIntegralModelGeometry) :
    (D.canonicalPeriodData hg x).periodTorus ≃+ (F.toNativeReference D).periodData.periodTorus :=
  Torus.LinearEquiv.torusLinearEquiv (D.canonicalPeriodData hg x) (F.toNativeReference D).periodData
    (F.periodComparison D hg) (F.periodComparison_mem D hg)

def Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.canonicalTorusDiffeomorph (hg : D.pel.HasIntegralModelGeometry) :
    (D.canonicalPeriodData hg x).periodTorus ≃ₘ⟮𝓘(ℂ, (D.canonicalPeriodData hg x).space),
      𝓘(ℂ, (F.toNativeReference D).periodData.space)⟯ (F.toNativeReference D).periodData.periodTorus :=
  Torus.LinearEquiv.torusLinearDiffeomorph (D.canonicalPeriodData hg x) (F.toNativeReference D).periodData
    (F.periodComparison D hg) (F.periodComparison_mem D hg)

theorem Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.canonicalTorusDiffeomorph_mk (hg : D.pel.HasIntegralModelGeometry)
    (v : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :
    F.canonicalTorusDiffeomorph D hg (QuotientAddGroup.mk v) =
      QuotientAddGroup.mk (F.periodComparison D hg v) := rfl

theorem Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.canonicalTorusEquiv_add (hg : D.pel.HasIntegralModelGeometry)
    (u v : (D.canonicalPeriodData hg x).periodTorus) :
    F.canonicalTorusDiffeomorph D hg (u + v) =
      F.canonicalTorusDiffeomorph D hg u + F.canonicalTorusDiffeomorph D hg v :=
  (F.canonicalTorusEquiv D hg).map_add u v

end

end OAI.RepresentationTheory.Theta.Geometric
