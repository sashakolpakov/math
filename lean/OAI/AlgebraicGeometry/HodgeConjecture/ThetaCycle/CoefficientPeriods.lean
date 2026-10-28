import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Prescribed
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoordinateComparison

/-! # Coefficient Periods -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoefficientPeriods.CM

noncomputable section

section

/-! The explicit line/annihilator frame is holomorphic, has the prescribed
range, and has a positive isotropic matrix in the constructed coordinates. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]

def ballMatrix (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K) :=
  Geometry.ComplexBall.PrescribedSignsB.matrixB (HeckeCycles.ReferenceDatum.CM.embeddings K places) (Matrix.diagonal ![1, 1, B.b])

theorem ball_frame_denominator (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K) (z : HeckeCycles.GeometricSource.CM.BallChart) :
    ballMatrix K B places places.distinguished (Geometry.ComplexBall.PrescribedSignsB.lineVector z)
      (Geometry.ComplexBall.PrescribedSignsB.axis 2) ≠ 0 := by
  have he : ballMatrix K B places places.distinguished (Geometry.ComplexBall.PrescribedSignsB.lineVector z)
      (Geometry.ComplexBall.PrescribedSignsB.axis 2) = (B.b : ℂ) := by
    simp [ballMatrix, Geometry.ComplexBall.PrescribedSignsB.matrixB_apply, NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.localB_diagonal,
      Geometry.ComplexBall.PrescribedSignsB.axis, Geometry.ComplexBall.PrescribedSignsB.lineVector, HeckeCycles.ReferenceDatum.CM.embeddings_distinguished]
  rw [he]
  intro hz
  have hn := B.negative
  simp only [hz, Complex.zero_re, lt_self_iff_false] at hn

theorem native_frame_range (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Gal(K/ℚ) → Bool) (z : HeckeCycles.GeometricSource.CM.BallChart) (w : HeckeCycles.GeometricSource.CM.Ambient K) :
    w ∈ LinearMap.range (Prescribed.CM.nativePeriodFrame K B places d z) ↔
      HeckeCycles.GeometricSource.CM.prescribed K B places d z w := by
  have hr := Geometry.ComplexBall.PrescribedSignsB.globalFrame_range (ballMatrix K B places)
    places.distinguished (fun i => d (places.representative i)) z
    (ball_frame_denominator K B places z) (Symplectic.CM.galoisToPaired K places w)
  simp only [ballMatrix, Geometry.ComplexBall.PrescribedSignsB.matrixB_apply] at hr
  change Symplectic.CM.galoisToPaired K places w ∈ LinearMap.range
    (Geometry.ComplexBall.PrescribedSignsB.globalFrame (ballMatrix K B places) places.distinguished
      (fun i => d (places.representative i)) z) ↔
    Geometry.ComplexBall.PrescribedSignsB.Prescribed (Lagrangians.CM.pairedBallForm K B places) places.distinguished
      (fun i => d (places.representative i)) z (Symplectic.CM.galoisToPaired K places w) at hr
  rw [← Prescribed.CM.paired_prescribed_iff K B places d z w, ← hr]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨fun i j => v (i, j), ?_⟩
    change _ = (Symplectic.CM.galoisToPaired K places)
      ((Symplectic.CM.galoisToPaired K places).symm (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.flatFrame _ _ _ z v))
    rw [LinearEquiv.apply_symm_apply]
    rfl
  · rintro ⟨v, hv⟩
    refine ⟨fun p => v p.1 p.2, ?_⟩
    apply (Symplectic.CM.galoisToPaired K places).injective
    change (Symplectic.CM.galoisToPaired K places) ((Symplectic.CM.galoisToPaired K places).symm
      (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.flatFrame _ _ _ z (fun p => v p.1 p.2))) = _
    rw [LinearEquiv.apply_symm_apply]
    exact hv

theorem native_frame_holomorphic (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Gal(K/ℚ) → Bool) (v : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    DifferentiableOn ℂ (fun z => Prescribed.CM.nativePeriodFrame K B places d z v) B.domain := by
  have hf := Geometry.ComplexBall.PrescribedSignsB.globalFrame_differentiable (ballMatrix K B places)
    places.distinguished (fun i => d (places.representative i)) B.domain
    (fun z _ => ball_frame_denominator K B places z) (fun i j => v (i, j))
  exact (Symplectic.CM.galoisToPaired K places).symm.toContinuousLinearEquiv.differentiable.comp_differentiableOn hf

theorem constructed_global_frame_positive (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Fin 2 → Fin places.count → Bool) (P : Lagrangians.CM.LagrangianPair K B places d)
    (i : Fin 2) (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    Geometry.ComplexBall.PrescribedSignsB.PositivePeriod (3 * Fintype.card (Fin places.count))
      (Geometry.ComplexBall.PrescribedSignsB.tracePairing (Lagrangians.CM.pairedBallForm K B places)
        (fun τ => HeckeCycles.ReferenceDatum.CM.embeddings K places τ (P.delta * P.a i)))
      Geometry.ComplexBall.PrescribedSignsB.realConj
      (LinearMap.range (Geometry.ComplexBall.PrescribedSignsB.globalFrame (ballMatrix K B places)
        places.distinguished (d i) z)) := by
  have hr : LinearMap.range (Geometry.ComplexBall.PrescribedSignsB.globalFrame (ballMatrix K B places)
      places.distinguished (d i) z) = P.family i z := by
    ext u
    have h := Geometry.ComplexBall.PrescribedSignsB.globalFrame_range (ballMatrix K B places)
      places.distinguished (d i) z (ball_frame_denominator K B places z) u
    simp only [ballMatrix, Geometry.ComplexBall.PrescribedSignsB.matrixB_apply] at h
    exact h.trans ((P.prescribed_positive i z hz).1 u).symm
  rw [hr, Fintype.card_fin]
  exact (P.prescribed_positive i z hz).2

end

/-! Build the prescribed period pair with specified Hermitian coefficients.
This permits the new rational lines to retain the original trace polarization. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]

theorem positive_period_of_coefficient_signs (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Fin places.count → Bool) (δ a : K)
    (hδ : ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K δ = -δ) (ha : ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K a = a)
    (hs : ∀ τ, if τ = places.distinguished ∨ d τ = true
      then (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (δ * a)).im < 0
      else 0 < (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (δ * a)).im)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    Geometry.ComplexBall.PrescribedSignsB.PositivePeriod (3 * places.count)
      (Geometry.ComplexBall.PrescribedSignsB.tracePairing (Lagrangians.CM.pairedBallForm K B places)
        (fun τ => HeckeCycles.ReferenceDatum.CM.embeddings K places τ (δ * a))) Geometry.ComplexBall.PrescribedSignsB.realConj
      (LinearMap.range (Geometry.ComplexBall.PrescribedSignsB.globalFrame (ballMatrix K B places)
        places.distinguished d z)) := by
  let BM := ballMatrix K B places
  have hBM (τ : Fin places.count) : Geometry.ComplexBall.PrescribedSignsB.HermitianB (BM τ) :=
    Geometry.ComplexBall.PrescribedSignsB.matrixB_hermitian (HeckeCycles.ReferenceDatum.CM.embeddings K places)
      (Matrix.diagonal ![1, 1, B.b]) (NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.diagonal_hermitian B.b B.conjugate_b) τ
  have hc (τ : Fin places.count) (hτ : τ ≠ places.distinguished) :
      Geometry.ComplexBall.PrescribedSignsB.PositiveB (BM τ) := by
    intro x hx
    simpa only [BM, ballMatrix, Geometry.ComplexBall.PrescribedSignsB.matrixB_apply] using
      NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.diagonal_positive_definite (HeckeCycles.ReferenceDatum.CM.embeddings K places) B.b τ
        ((HeckeCycles.ReferenceDatum.CM.source_signature K B places).2.2.2 τ hτ) x hx
  have hp : ∀ x : Geometry.ComplexBall.PrescribedSignsB.Vec, x ≠ 0 → x 2 = 0 →
      0 < (BM places.distinguished x (star x)).re := by
    intro x hx hx2
    simpa only [BM, ballMatrix, Geometry.ComplexBall.PrescribedSignsB.matrixB_apply] using
      NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.diagonal_positive_plane
        (HeckeCycles.ReferenceDatum.CM.embeddings K places) B.b places.distinguished x hx hx2
  have ht (τ : Fin places.count) : (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (δ * a)).re = 0 :=
    Geometry.ComplexBall.PrescribedSignsB.coefficient_real_zero (HeckeCycles.ReferenceDatum.CM.embeddings K places τ) δ a hδ ha
  have hsign (τ : Fin places.count) :
      if Geometry.ComplexBall.PrescribedSignsB.wantedSign BM places.distinguished d τ
        then 0 < (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (δ * a)).im
        else (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (δ * a)).im < 0 := by
    by_cases hτ : τ = places.distinguished
    · simpa [Geometry.ComplexBall.PrescribedSignsB.wantedSign, hτ] using hs τ
    · cases hd : d τ <;>
        simpa [Geometry.ComplexBall.PrescribedSignsB.wantedSign, hτ, hd, hc τ hτ] using hs τ
  have hz' : (BM places.distinguished (Geometry.ComplexBall.PrescribedSignsB.lineVector z)
      (star (Geometry.ComplexBall.PrescribedSignsB.lineVector z))).re < 0 := by
    have hz'' : z ∈ {w : HeckeCycles.GeometricSource.CM.BallChart | (Lagrangians.CM.pairedBallForm K B places places.distinguished
        (Geometry.ComplexBall.PrescribedSignsB.lineVector w) (star (Geometry.ComplexBall.PrescribedSignsB.lineVector w))).re < 0} := by
      rw [Lagrangians.CM.paired_ball_domain K B places]
      exact hz
    simpa only [BM, ballMatrix, Geometry.ComplexBall.PrescribedSignsB.matrixB_apply, Lagrangians.CM.pairedBallForm,
      Set.mem_ofPred_eq] using hz''
  have hpositive := Geometry.ComplexBall.PrescribedSignsB.globalFrame_positivePeriod BM hBM
    places.distinguished d z (ball_frame_denominator K B places z)
    (fun τ => HeckeCycles.ReferenceDatum.CM.embeddings K places τ (δ * a)) ht (by
      intro τ u hu hne
      exact Geometry.ComplexBall.PrescribedSignsB.wantedSign_positive BM hBM places.distinguished hp
        (fun τ hτ => Or.inl (hc τ hτ)) d z hz' (ball_frame_denominator K B places z)
        τ _ (ht τ) (hsign τ) u hu hne)
  simpa only [Fintype.card_fin, BM, ballMatrix, Geometry.ComplexBall.PrescribedSignsB.matrixB_apply,
    Lagrangians.CM.pairedBallForm] using hpositive

theorem exists_lagrangian_pair_with_coefficients (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Fin 2 → Fin places.count → Bool) (δ : K) (a : Fin 2 → K)
    (hδ0 : δ ≠ 0) (hδ : ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K δ = -δ)
    (ha0 : ∀ i, a i ≠ 0) (ha : ∀ i, ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K (a i) = a i)
    (hs : ∀ i τ, if τ = places.distinguished ∨ d i τ = true
      then (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (δ * a i)).im < 0
      else 0 < (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (δ * a i)).im) :
    ∃ P : Lagrangians.CM.LagrangianPair K B places d, P.delta = δ ∧ P.a = a := by
  obtain ⟨Q⟩ := Lagrangians.CM.exists_lagrangian_pair K B places d
  have hr (i : Fin 2) (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
      LinearMap.range (Geometry.ComplexBall.PrescribedSignsB.globalFrame (ballMatrix K B places)
        places.distinguished (d i) z) = Q.family i z := by
    ext u
    have h := Geometry.ComplexBall.PrescribedSignsB.globalFrame_range (ballMatrix K B places)
      places.distinguished (d i) z (ball_frame_denominator K B places z) u
    simp only [ballMatrix, Geometry.ComplexBall.PrescribedSignsB.matrixB_apply] at h
    exact h.trans ((Q.prescribed_positive i z hz).1 u).symm
  have hpositive (i : Fin 2) (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
      Geometry.ComplexBall.PrescribedSignsB.PositivePeriod (3 * places.count)
        (Geometry.ComplexBall.PrescribedSignsB.tracePairing (Lagrangians.CM.pairedBallForm K B places)
          (fun τ => HeckeCycles.ReferenceDatum.CM.embeddings K places τ (δ * a i))) Geometry.ComplexBall.PrescribedSignsB.realConj
        (Q.family i z) := by
    rw [← hr i z hz]
    exact positive_period_of_coefficient_signs K B places (d i) δ (a i) hδ (ha i) (hs i) z hz
  refine ⟨{
    delta := δ
    delta_ne_zero := hδ0
    delta_imaginary := hδ
    a := a
    a_sign := fun i => ⟨ha0 i, ha i, by simpa using hs i places.distinguished⟩
    family := Q.family
    holomorphic := Q.holomorphic
    prescribed_positive := fun i z hz => ⟨(Q.prescribed_positive i z hz).1, hpositive i z hz⟩
    total_holomorphic := Q.total_holomorphic
    total_positive := ?_
    rational_trace := ?_
  }, rfl, rfl⟩
  · intro z hz
    apply Geometry.ComplexBall.PrescribedSignsB.positivePeriod_prod (3 * places.count) _ _
      (Geometry.ComplexBall.PrescribedSignsB.realConjLinearMap (Fin places.count))
      (Geometry.ComplexBall.PrescribedSignsB.realConjLinearMap (Fin places.count)) _ _
      _ (hpositive 0 z hz) (hpositive 1 z hz)
    simp [Geometry.ComplexBall.PrescribedSignsB.Ambient, Geometry.ComplexBall.PrescribedSignsB.Vec,
      Module.finrank_pi_fintype, Module.finrank_prod]
    omega
  · intro i x y
    have h := Geometry.ComplexBall.PrescribedSignsB.tracePairing_rational (HeckeCycles.ReferenceDatum.CM.embeddings K places)
      (HeckeCycles.ReferenceDatum.CM.embeddings_complete K places) δ (a i) hδ (ha i)
      (Matrix.diagonal ![1, 1, B.b]) (NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.diagonal_hermitian B.b B.conjugate_b) x y
    rw [NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.trace_matrix_diagonal] at h
    exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoefficientPeriods.CM
