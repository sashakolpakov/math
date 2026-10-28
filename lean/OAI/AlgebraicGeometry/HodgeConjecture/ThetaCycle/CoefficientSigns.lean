import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Lagrangians

/-! # Coefficient Signs -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoefficientSigns.CM

noncomputable section

/-! Recover the multiplicity coefficients' signs from the actual positive
Lagrangians, using a nonzero vector at each compact place. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}

def compactTestVector (d : Fin places.count → Bool) (τ : Fin places.count) :
    Lagrangians.CM.pairedAmbient K places :=
  Pi.single τ (if d τ then (0, ![1, 0, 0]) else (![1, 0, 0], 0))

theorem compact_test_prescribed (d : Fin places.count → Bool)
    (τ : Fin places.count) (hτ : τ ≠ places.distinguished) (z : HeckeCycles.GeometricSource.CM.BallChart) :
    Geometry.ComplexBall.PrescribedSignsB.Prescribed (Lagrangians.CM.pairedBallForm K B places)
      places.distinguished d z (compactTestVector K d τ) := by
  intro j
  by_cases hj : j = τ
  · subst j
    cases hd : d τ <;>
      simp [compactTestVector, hτ, hd]
  · simp only [compactTestVector, Pi.single_eq_of_ne hj, Prod.fst_zero, Prod.snd_zero]
    split_ifs
    · exact ⟨Submodule.zero_mem _, by simp [Lagrangians.CM.pairedBallForm, Geometry.ComplexBall.PrescribedSignsB.localB]⟩

omit [IsGalois ℚ K] in
theorem compact_test_ne_zero (d : Fin places.count → Bool) (τ : Fin places.count) :
    compactTestVector K d τ ≠ 0 := by
  intro h
  have hτ := congrFun h τ
  cases hd : d τ <;> simp [compactTestVector, hd] at hτ

theorem compact_test_pairing (d : Fin places.count → Bool) (τ : Fin places.count)
    (t : Fin places.count → ℂ) :
    Geometry.ComplexBall.PrescribedSignsB.tracePairing (Lagrangians.CM.pairedBallForm K B places) t
      (compactTestVector K d τ) (Geometry.ComplexBall.PrescribedSignsB.realConj (compactTestVector K d τ)) =
      if d τ then -(t τ) else t τ := by
  unfold Geometry.ComplexBall.PrescribedSignsB.tracePairing
  rw [Finset.sum_eq_single τ]
  · cases hd : d τ <;>
      simp [Geometry.ComplexBall.PrescribedSignsB.realConj, compactTestVector, hd,
        Lagrangians.CM.pairedBallForm, NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.localB_diagonal]
  · intro j _ hj
    simp [Geometry.ComplexBall.PrescribedSignsB.realConj, compactTestVector, Pi.single_eq_of_ne hj,
      Lagrangians.CM.pairedBallForm, NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.localB_diagonal]
  · simp

theorem lagrangian_compact_coefficient_sign
    (d : Fin 2 → Fin places.count → Bool) (P : Lagrangians.CM.LagrangianPair K B places d)
    (i : Fin 2) (τ : Fin places.count) (hτ : τ ≠ places.distinguished) :
    if d i τ then (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (P.delta * P.a i)).im < 0
      else 0 < (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (P.delta * P.a i)).im := by
  have hz : (0 : HeckeCycles.GeometricSource.CM.BallChart) ∈ B.domain := by
    change Complex.normSq 0 + Complex.normSq 0 < -(B.b : ℂ).re
    simpa only [Complex.normSq_zero, zero_add] using neg_pos.mpr B.negative
  have hmem := ((P.prescribed_positive i 0 hz).1 (compactTestVector K (d i) τ)).mpr
    (compact_test_prescribed K (d i) τ hτ 0)
  have hp := ((P.prescribed_positive i 0 hz).2.2.2.2.1
    (compactTestVector K (d i) τ) hmem (compact_test_ne_zero K (d i) τ)).2
  rw [compact_test_pairing] at hp
  cases hd : d i τ <;>
    simp only [hd, Bool.false_eq_true, ite_false, ite_true, Complex.div_I,
      Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero,
      mul_one, zero_sub, neg_neg, Complex.neg_im] at hp ⊢
  · exact hp
  · linarith

theorem multiplicity_sign_orientation
    (d : Fin 2 → Fin places.count → Bool) (P : Lagrangians.CM.LagrangianPair K B places d)
    (hμ : ∀ i, d i places.distinguished = true) :
    (∀ τ, -(HeckeCycles.ReferenceDatum.CM.embeddings K places τ P.delta).im ≠ 0) ∧
      ∀ i τ, 0 < (ComplexMultiplication.SignSwitch.CM.signValue (d i τ) : ℝ) *
        (-(HeckeCycles.ReferenceDatum.CM.embeddings K places τ P.delta).im) * (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (P.a i)).re := by
  have hre (τ : Fin places.count) : (HeckeCycles.ReferenceDatum.CM.embeddings K places τ P.delta).re = 0 := by
    have hc := NumberField.IsCMField.complexEmbedding_complexConj K
      (HeckeCycles.ReferenceDatum.CM.embeddings K places τ).toRingHom P.delta
    rw [show NumberField.IsCMField.complexConj K P.delta = -P.delta from P.delta_imaginary,
      map_neg] at hc
    have hh := congrArg Complex.re hc
    simp only [Complex.neg_re, Complex.conj_re] at hh
    change -(HeckeCycles.ReferenceDatum.CM.embeddings K places τ P.delta).re = (HeckeCycles.ReferenceDatum.CM.embeddings K places τ P.delta).re at hh
    linarith
  have him (i : Fin 2) (τ : Fin places.count) : (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (P.a i)).im = 0 := by
    have hc := NumberField.IsCMField.complexEmbedding_complexConj K
      (HeckeCycles.ReferenceDatum.CM.embeddings K places τ).toRingHom (P.a i)
    rw [show NumberField.IsCMField.complexConj K (P.a i) = P.a i from (P.a_sign i).2.1] at hc
    have hh := congrArg Complex.im hc
    simp only [Complex.conj_im] at hh
    change (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (P.a i)).im = -(HeckeCycles.ReferenceDatum.CM.embeddings K places τ (P.a i)).im at hh
    linarith
  constructor
  · intro τ hzero
    apply P.delta_ne_zero
    apply (HeckeCycles.ReferenceDatum.CM.embeddings K places τ).injective
    rw [map_zero]
    apply Complex.ext (hre τ)
    exact neg_eq_zero.mp hzero
  · intro i τ
    have hs : if d i τ then (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (P.delta * P.a i)).im < 0
        else 0 < (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (P.delta * P.a i)).im := by
      by_cases hτ : τ = places.distinguished
      · subst τ
        simpa only [hμ i, ite_true] using (P.a_sign i).2.2
      · exact lagrangian_compact_coefficient_sign K d P i τ hτ
    rw [map_mul, Complex.mul_im, him, mul_zero, zero_add] at hs
    cases hd : d i τ <;> simp only [hd, Bool.false_eq_true, ite_false, ite_true] at hs
      <;> simp [ComplexMultiplication.SignSwitch.CM.signValue] <;> nlinarith

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoefficientSigns.CM
