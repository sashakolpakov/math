import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HarmonicOneForms
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TwoFormEnergy

/-! # Antiholomorphic Closed Representative -/

namespace OAI.RepresentationTheory.Theta.Geometric.AntiholomorphicClosedRepresentative

noncomputable section

section

/-! The actual projective Poisson solution corrects the antiholomorphic
part of a one-form. The conjugate energy identity detects closedness. -/

open scoped _root_.Manifold ContDiff

theorem exists_antiholomorphic_coclosed_correction (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) :
    ∃ f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0,
      Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0
        (a - (2 : ℂ) • AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.oneFormAntiholomorphicPart (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f)) = 0 := by
  obtain ⟨f, hf⟩ := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HarmonicOneForms.CM.Construction.exists_smooth_coclosed_correction V (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CompactMetricCover.CM.Construction.projectiveCompactMetricCover V)
    (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) a
  have heq := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ClosedOneCodifferentialParts.CM.Construction.closed_oneForm_codifferential_parts V (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f)
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_squared f)
  have hsum := congrArg (Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0)
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.oneForm_parts_add (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f))
  rw [map_add, heq] at hsum
  rw [map_sub] at hf
  refine ⟨f, ?_⟩
  rw [map_sub, map_smul, sub_eq_zero.mp hf, ← hsum, two_smul, sub_self]

theorem conjugate_type11 (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 1 a.val) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 1 (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm a).val := by
  intro e he y hy z v
  change star (a.val.inChart e y (fun i => (z : ℂ) • v i)) =
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 1 1 z * star (a.val.inChart e y v)
  rw [ha e he y hy z v, star_mul]
  simp only [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_one, star_mul, star_star]
  ring

theorem coclosed_type01_mixed_derivative_zero (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 0 1 a.val)
    (hd : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 1 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val)
    (hc : Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 a = 0) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0 := by
  have hdc : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 1
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm a)).val := by
    rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.d_conjugateSmoothForm]
    exact conjugate_type11 V (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) hd
  have hcc : Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm a) = 0 := by
    rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AdjointConjugation.CM.Construction.projectiveCodifferential_conjugate, hc, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm_zero]
  have h := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TwoFormEnergy.CM.Construction.coclosed_type10_mixed_derivative_zero V (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm a)
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AntiholomorphicCodifferential.CM.Construction.conjugateSmoothForm_antiholomorphic_is_holomorphic V a ha) hdc hcc
  rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.d_conjugateSmoothForm] at h
  have H := congrArg AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm h
  simpa only [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm_involutive, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm_zero] using H

end

/-! On the actual projective manifold every dbar-closed (0,1)-form
differs from a d-closed (0,1)-form by the dbar derivative of a scalar. -/

open scoped _root_.Manifold ContDiff

theorem antiholomorphicPart_d_eq_dbar (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.oneFormAntiholomorphicPart (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f) =
      (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.zeroFormPure f)).val := by
  have h := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.oneForm_parts_add (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f)
  rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.oneFormHolomorphicPart_d_eq_dPrime] at h
  have hd := Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime_add_dDoublePrime (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.zeroFormPure f)
  simp only [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_self] at hd
  exact add_left_cancel (h.trans hd.symm)

theorem type01_dbar_zero_exterior_type11 (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm V.analyticModel V.analyticSpace 0 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime a = 0) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 1 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a.val).val := by
  have h := Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime_add_dDoublePrime a
  simp only [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_self, ha, ZeroMemClass.coe_zero, add_zero] at h
  rw [← h]
  exact (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime a).property

theorem exists_closed_antiholomorphic_representative (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm V.analyticModel V.analyticSpace 0 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime a = 0) :
    ∃ (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0)
      (b : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm V.analyticModel V.analyticSpace 0 1),
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b.val = 0 ∧
      a = b + (2 : ℂ) • Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.zeroFormPure f) := by
  obtain ⟨f, hf⟩ := exists_antiholomorphic_coclosed_correction V a.val
  let b := a - (2 : ℂ) • Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.zeroFormPure f)
  have hb : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime b = 0 := by
    dsimp only [b]
    rw [map_sub, map_smul, ha, Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime_squared, smul_zero, sub_zero]
  have hc : Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 b.val = 0 := by
    change Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0
      (a.val - (2 : ℂ) • (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.zeroFormPure f)).val) = 0
    rw [← antiholomorphicPart_d_eq_dbar V f]
    exact hf
  refine ⟨f, b, coclosed_type01_mixed_derivative_zero V b.val b.property
    (type01_dbar_zero_exterior_type11 V b hb) hc, ?_⟩
  dsimp only [b]
  exact (sub_add_cancel a _).symm

theorem closed_dbar_scalar_eq_zero (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0)
    (hf : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.zeroFormPure f)).val = 0) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.zeroFormPure f) = 0 := by
  have h := congrArg Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.oneForm_parts_add (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f))
  rw [map_add, antiholomorphicPart_d_eq_dbar V f, hf, add_zero, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_squared] at h
  have hd := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.scalar_correction_kernel f h
  apply Subtype.ext
  rw [← antiholomorphicPart_d_eq_dbar V f, hd, map_zero]
  rfl

theorem closed_type01_unique_mod_dbar (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a b : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm V.analyticModel V.analyticSpace 0 1)
    (ha : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a.val = 0) (hb : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b.val = 0)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0)
    (h : a = b + Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.zeroFormPure f)) : a = b := by
  have hd := congrArg (fun a : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm V.analyticModel V.analyticSpace 0 1 =>
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a.val) h
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a.val = Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d
    (b.val + (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.zeroFormPure f)).val) at hd
  rw [map_add, ha, hb] at hd
  have hd' : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.zeroFormPure f)).val = 0 :=
    (zero_add _).symm.trans hd.symm
  have hz := closed_dbar_scalar_eq_zero V f hd'
  exact (h.trans (congrArg (fun u => b + u) hz)).trans (add_zero b)

end

end OAI.RepresentationTheory.Theta.Geometric.AntiholomorphicClosedRepresentative
