import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointProjectiveCoefficientNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.ProjectiveTransport

/-! # Projective Transport Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.ProjectiveTransportNaturality

noncomputable section

/-! Canonical projective transport of framed configurations
commutes with coefficient change. This applies to the actual
stable-chart intersection isomorphisms. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v
variable {A B : Type u} [CommRing A] [CommRing B] {n : ℕ} {ι : Type v}

theorem configurationProjectiveTransport_coefficient_natural
    (φ : A →+* B) (v w : ι → Fin (n + 1) → A) (h : ProjectiveTransport.ConfigurationFrameRelated v w)
    (σ : Fin (n + 1) → ι) (b : ι)
    (hv : IsUnit (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant (Pi.basisFun A (Fin (n + 1))) (fun k => v (σ k)) (v b))) :
    (ProjectiveTransport.configurationProjectiveTransport (fun z i => φ (v z i)) (fun z i => φ (w z i)) (h.map φ)).hom.left ≫
        Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n =
      Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n ≫ (ProjectiveTransport.configurationProjectiveTransport v w h).hom.left := by
  obtain ⟨T, s, hs⟩ := h
  have hB : IsUnit (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant (Pi.basisFun B (Fin (n + 1)))
      (fun k i => φ (v (σ k) i)) (fun i => φ (v b i))) := by
    change IsUnit (ProjectiveFrame.Polynomials.vectorFrameDiscriminant (fun k i => φ (v (σ k) i)) (fun i => φ (v b i)))
    rw [← ProjectiveFrame.Polynomials.vectorFrameDiscriminant_map]
    exact hv.map φ
  have hsB : ∀ z, (fun i => φ (w z i)) = (Units.map φ.toMonoidHom (s z)).val •
      PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv φ T (fun i => φ (v z i)) := by
    intro z
    funext i
    change φ (w z i) = φ (s z) * PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv φ T (fun k => φ (v z k)) i
    rw [PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv_apply_map]
    exact (congrArg φ (congrFun (hs z) i)).trans (map_mul φ _ _)
  let hrel : ProjectiveTransport.ConfigurationFrameRelated v w := ⟨T, s, hs⟩
  have h₁ := congrArg Over.Hom.left (ProjectiveTransport.configurationProjectiveTransport_eq_of_choice
    (fun z i => φ (v z i)) (fun z i => φ (w z i)) (hrel.map φ) σ b hB
    (PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv φ T) (fun z => Units.map φ.toMonoidHom (s z)) hsB)
  have h₂ := congrArg Over.Hom.left (ProjectiveTransport.configurationProjectiveTransport_eq_of_choice v w hrel σ b hv T s hs)
  rw [h₁, h₂]
  exact PointProjectiveCoefficientNaturality.pointCoordinateProjectiveIso_coefficient_natural φ T

variable (R : Type u) [CommRing R] [Algebra R A] [Algebra R B]
variable {m : ℕ} (i : Fin m) (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)

theorem stableChartIntersectionProjectiveIso_natural
    (ρ : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i (j.intersection k).exponent (j.intersection k).balanced →ₐ[R] A)
    (φ : A →ₐ[R] B) :
    (StableIntersection.ProjectiveTransport.stableChartIntersectionProjectiveIso R i j k (φ.comp ρ)).hom.left ≫
        Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ.toRingHom) n =
      Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ.toRingHom) n ≫
        (StableIntersection.ProjectiveTransport.stableChartIntersectionProjectiveIso R i j k ρ).hom.left := by
  exact configurationProjectiveTransport_coefficient_natural φ.toRingHom
    (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i j
      (ρ.comp (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionLeftAlg R i j.exponent k.exponent j.balanced k.balanced)))
    (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i k
      (ρ.comp (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionRightAlg R i j.exponent k.exponent j.balanced k.balanced)))
    (StableIntersection.ProjectiveTransport.stableChartIntersection_frameRelated R i j k ρ) j.frame j.additional
    (Stable.NormalizedFrameRelation.stableChartNormalizedPoint_hasFrame R i j _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.ProjectiveTransportNaturality
