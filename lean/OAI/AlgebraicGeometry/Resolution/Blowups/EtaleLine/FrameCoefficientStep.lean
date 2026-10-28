import OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.FrameCenterPermissibility
import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.FrameCenterSmooth
import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.RatioRetraction
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.BlowupChart

/-! # Frame Coefficient Step -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.FrameCoefficientStep.Construction

noncomputable section

/-! A complete actual coefficient step with smooth centers, smooth charts, and retained coefficient data. -/

open _root_.Polynomial _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) {H R ι : Type u} {τ : Type*}
  [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [CommRing R]
  [Algebra k H] [Algebra k R] [Algebra H R] [IsScalarTower k H R]
  [Algebra H[X] R] [IsScalarTower H H[X] R] [Algebra.Etale H[X] R]
  [Algebra.Smooth k H] [Algebra ℚ R] [Fintype ι] [DecidableEq ι]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartBaseAlgebra
  Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartCoordinateAlgebra Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChart_scalarTower Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChart_algebra_etale
  ReferenceBase.Construction.etaleLineChart_originalScalarTower HorizontalDerivation.Construction.etaleLine_polynomial_originalScalarTower

/-- The retained coefficient bound constructs a permissible smooth center
and proves smoothness of its actual entire lifted blowup. -/
theorem etaleLine_frame_coefficient_center
    (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H) (p : τ → R) (b : ℕ)
    (g : ι → H) (δ : ι → Derivation k H H)
    (hδ : ∀ i j, δ i (g j) = if i = j then 1 else 0)
    (C : Ideal (R ⧸ Ideal.span {algebraMap H[X] R X}))
    (hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal (Retracted.CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := H) (R := R))
      (algebraMap H[X] R X) p b ≤ C)
    (hC : C.map e.toRingHom ≤ (Ideal.span (Set.range g)) ^ b.factorial) :
    let I := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) (Ideal.span (Set.range g))
    Ideal.span (Set.range p) ≤ I ^ b ∧ Algebra.Smooth k (R ⧸ I) ∧
      Smooth (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  let K := Ideal.span (Set.range g)
  have hI : Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) K = K.map (algebraMap H R) ⊔ Ideal.span {algebraMap H[X] R X} := by
    rw [RetractionStep.Construction.etaleLineCenter_eq, NormalDerivation.Construction.etaleLineCoefficientMap_eq]
  obtain ⟨hperm, hsmooth⟩ := Retracted.FrameCenterPermissibility.Construction.retracted_frame_coefficient_center_permissible k
    (Retracted.CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := H) (R := R)) (algebraMap H[X] R X)
    (Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation_coordinate (H := H) (V := R)) e p b g δ hδ C hlow hC
  exact ⟨hI.symm ▸ hperm, hI.symm ▸ hsmooth, FrameCenterSmooth.Construction.etaleLine_frame_center_blowup_smooth k g δ hδ⟩

variable [IsNoetherianRing R]

/-- Every coefficient-denominator chart has a smooth actual coefficient
ring and ambient ring, retains the normal-family interval, and identifies
its coefficient ideal with the exact fixed-control transform on the coefficient blowup. -/
theorem etaleLine_frame_coefficient_step
    (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H) (p : τ → R) (b : ℕ)
    (g : ι → H) (δ : ι → Derivation k H H)
    (hδ : ∀ i j, δ i (g j) = if i = j then 1 else 0)
    (C : Ideal (R ⧸ Ideal.span {algebraMap H[X] R X}))
    (hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal (Retracted.CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := H) (R := R))
      (algebraMap H[X] R X) p b ≤ C)
    (hupp : C ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (algebraMap H[X] R X) (Ideal.span (Set.range p)) b)
    (hC : C.map e.toRingHom ≤ (Ideal.span (Set.range g)) ^ b.factorial) :
    let K := Ideal.span (Set.range g)
    let I := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) K
    ∃ hp : Ideal.span (Set.range p) ≤ I ^ b,
      Algebra.Smooth k (R ⧸ I) ∧
      Smooth (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) ∧
      ∀ a : K,
        let p' := ControlledGeneratorFamily.Construction.blowupChartTransformFamily I p (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a) b hp
        let C' := RatioRetraction.Construction.etaleLineTransformedCoefficientIdeal K a C b.factorial
        Algebra.Smooth k (Blowup.Charts.Construction.blowupChart K a) ∧ Algebra.Smooth k (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a) ∧
        (WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal
          (Retracted.CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := Blowup.Charts.Construction.blowupChart K a) (R := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a))
          (RatioRetraction.Construction.etaleLineRatioCoordinate (R := R) K a) p' b ≤ C' ∧
          C' ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (RatioRetraction.Construction.etaleLineRatioCoordinate (R := R) K a)
            (Ideal.span (Set.range p')) b) ∧
        C'.map (RatioRetraction.Construction.etaleLineRatioFiberEquiv e K a).toRingHom =
          ControlledTransform.Construction.blowupControlledTransform K (C.map e.toRingHom) b.factorial a := by
  let K := Ideal.span (Set.range g)
  let I := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) K
  obtain ⟨hp, hsmooth, hblowup⟩ := etaleLine_frame_coefficient_center k e p b g δ hδ C hlow hC
  let : Smooth (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) := hblowup
  let : Smooth (ReesGrading.Construction.affineBlowupToSpec K ≫ Spec.map (CommRingCat.ofHom (algebraMap k H))) :=
    DualFrameBlowupSmooth.Construction.dual_derivation_family_blowup_smooth g δ hδ
  refine ⟨hp, hsmooth, hblowup, ?_⟩
  intro a
  exact ⟨Blowups.Smooth.BlowupChart.Construction.blowupChart_smooth_of_blowup_smooth k K a,
    Blowups.Smooth.BlowupChart.Construction.blowupChart_smooth_of_blowup_smooth k I (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a),
    Retracted.CoefficientStep.Construction.etaleLine_coefficient_interval_transform k K a p b hp C hlow hupp,
    RatioRetraction.Construction.etaleLineRatioFiberEquiv_controlledIdeal e K a C b.factorial⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.FrameCoefficientStep.Construction
