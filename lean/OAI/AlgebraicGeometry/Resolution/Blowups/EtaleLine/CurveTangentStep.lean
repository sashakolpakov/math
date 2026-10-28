import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.TangentCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.CurveFixedControlStep
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.CurveChart
import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.CurveCenterSmooth

/-! # Curve Tangent Step -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.CurveTangentStep.Construction

noncomputable section

/-! One actual curve-coefficient tangent step strictly decreases the retained differential bound. -/

open _root_.Polynomial _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartBaseAlgebra
  Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartCoordinateAlgebra Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChart_scalarTower Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChart_algebra_etale
  ReferenceBase.Construction.etaleLineChart_originalScalarTower HorizontalDerivation.Construction.etaleLine_polynomial_originalScalarTower

variable (k : Type u) {H R : Type u} {τ : Type*}
    [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [CommRing R]
    [Algebra k H] [Algebra k R] [Algebra H R] [IsScalarTower k H R]
    [Algebra H[X] R] [IsScalarTower H H[X] R] [Algebra.Etale H[X] R]
    [Algebra.Smooth k H] [Algebra ℚ R] [IsNoetherianRing R]

theorem etaleLine_curve_tangent_step
    (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H)
    (p : τ → R) (n ℓ : ℕ) (C : Ideal (R ⧸ Ideal.span {algebraMap H[X] R X}))
    (hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal
      (Retracted.CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := H) (R := R)) (algebraMap H[X] R X) p (n + 1) ≤ C)
    (hupp : C ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (algebraMap H[X] R X) (Ideal.span (Set.range p)) (n + 1))
    (hz : algebraMap H[X] R X ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Ideal.span (Set.range p)) n)
    (hdim : ringKrullDim H ≤ 1) (hlevel : (n + 1).factorial ≤ ℓ + 1)
    (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k C (ℓ + 1) = ⊤) :
    let K := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (C.map e.toRingHom) ℓ
    let I := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) K
    ∃ hp : Ideal.span (Set.range p) ≤ I ^ (n + 1),
      Algebra.Smooth k (R ⧸ I) ∧
      Smooth (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) ∧
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
        (ControlledTransform.Construction.blowupControlledTransform I (Ideal.span (Set.range p)) (n + 1) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement K)) n = ⊤ ∧
      ∀ a : K,
        let z' := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartCoordinateMap (R := R) K a X
        let p' := ControlledGeneratorFamily.Construction.blowupChartTransformFamily I p (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a) (n + 1) hp
        ∃ (e' : (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a ⧸ Ideal.span {z'}) ≃ₐ[Blowup.Charts.Construction.blowupChart K a] Blowup.Charts.Construction.blowupChart K a)
          (C' : Ideal (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a ⧸ Ideal.span {z'})),
          WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal
            (Retracted.CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := Blowup.Charts.Construction.blowupChart K a)
              (R := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a)) z' p' (n + 1) ≤ C' ∧
          C' ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z' (Ideal.span (Set.range p')) (n + 1) ∧
          C'.map e'.toRingHom = ControlledTransform.Construction.blowupControlledTransform K (C.map e.toRingHom) (n + 1).factorial a ∧
          Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k C' ℓ = ⊤ ∧
          z' ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Ideal.span (Set.range p')) n := by
  let B := C.map e.toRingHom
  let K := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k B ℓ
  let I := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) K
  let : Algebra.Smooth k (R ⧸ Ideal.span {algebraMap H[X] R X}) := Algebra.Smooth.of_equiv (e.restrictScalars k).symm
  let : Algebra ℚ H := ((algebraMap k H).comp (algebraMap ℚ k)).toAlgebra
  let : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  have hdQ : ringKrullDim (R ⧸ Ideal.span {algebraMap H[X] R X}) ≤ 1 :=
    e.toRingEquiv.ringKrullDim.le.trans hdim
  obtain ⟨_, hp, hsmooth, _, _⟩ := Curve.IntrinsicCoefficientCenter.Construction.curve_intrinsic_coefficient_center_lift k
    (Retracted.CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := H) (R := R)) (algebraMap H[X] R X)
    (Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation_coordinate (H := H) (V := R)) p (n + 1) ℓ hdQ C hlow hlevel hbound
  rw [← TangentCenter.Construction.etaleLine_tangent_center_eq_preimage k e C ℓ] at hp hsmooth
  have hb := Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k (e.restrictScalars k).toAlgHom
    (RingHom.Etale.of_bijective e.bijective) C (ℓ + 1)
  change (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k C (ℓ + 1)).map e.toRingHom =
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k B (ℓ + 1) at hb
  rw [hbound, Ideal.map_top] at hb
  obtain ⟨_, _, hπ, hdrop⟩ := Affine.CurveFixedControlStep.Construction.affine_curve_fixed_control_step k hdim B ℓ (n + 1).factorial
    (Nat.factorial_pos (n + 1)) hlevel hb.symm
  let : IsIso (ReesGrading.Construction.affineBlowupToSpec K) := hπ
  have hfirst : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k K = ⊤ :=
    (Curve.IntrinsicStep.Construction.first_iteratedRelativeDifferentialIdeal k B ℓ).trans hb.symm
  refine ⟨hp, hsmooth, CurveCenterSmooth.Construction.etaleLine_curve_center_blowup_smooth k K hdim hfirst,
    PersistentCoefficientStep.Construction.etaleLine_normal_chart_terminal k K (Ideal.span (Set.range p)) n hp hz, ?_⟩
  intro a
  obtain ⟨e', C', hl, hu, heq, hz'⟩ := PersistentCoefficientStep.Construction.etaleLine_persistent_coefficient_chart k e K a p n hp hz C hlow hupp
  refine ⟨e', C', hl, hu, heq, ?_, hz'⟩
  let : Algebra.Smooth k (Blowup.Charts.Construction.blowupChart K a) := Affine.CurveChart.Construction.blowupChart_smooth_of_isIso k K a
  let eₖ := e'.restrictScalars k
  let : Algebra.Smooth k (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a ⧸
      Ideal.span {Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartCoordinateMap (R := R) K a X}) := Algebra.Smooth.of_equiv eₖ.symm
  have hm := Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k eₖ.toAlgHom
    (RingHom.Etale.of_bijective e'.bijective) C' ℓ
  change (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k C' ℓ).map e'.toRingHom =
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (C'.map e'.toRingHom) ℓ at hm
  rw [heq, hdrop a] at hm
  exact (Ideal.map_eq_top_of_bijective e'.toRingHom e'.bijective).mp hm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.CurveTangentStep.Construction
