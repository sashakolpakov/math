import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumTensor
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleIntrinsicCotangentSlots
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection

/-! # Intrinsic Kernel Sum Slots -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumSlots.CM

noncomputable section

section

/-! The fixed source order-two slots are the literal native ThetaKernel slots,
with the two actual nonzero multiplicity scales retained. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

section

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d)

theorem direct_source_frame_coefficient_diagonal :
    SourceIntrinsicFrameDeterminant.CM.directSourceIndexedFrameCoefficientMatrix K Q =
      Matrix.diagonal (fun p : PeriodTotal.CM.TotalPositions K places =>
        SourceFrameComponents.CM.directSourceFrameScale K Q ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places) p).1
          ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places) p).2) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro u
  rw [SourceIntrinsicFrameDeterminant.CM.direct_source_indexed_frame_coefficient_apply]
  funext p
  rw [Matrix.mulVec_diagonal]
  cases p <;> rfl

end

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun k v => d k (places.representative v)))
  (hμ : ∀ k, d k (places.representative places.distinguished) = true)

theorem sum_comparison_dual_apply (u : PeriodTotal.CM.TotalPositions K places → ℂ)
    (p : Fin places.count × (Fin 3 × Fin 2)) :
    IntrinsicKernelSumTensor.CM.sumComparisonDualCoordinates K d Q u p =
      (SourceFrameComponents.CM.directSourceFrameScale K Q p.1 p.2)⁻¹ * u ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places).symm p) := by
  have hi : (SourceIntrinsicFrameDeterminant.CM.directSourceIndexedFrameCoefficientMatrix K Q)⁻¹ =
      Matrix.diagonal (fun p : PeriodTotal.CM.TotalPositions K places =>
        (SourceFrameComponents.CM.directSourceFrameScale K Q ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places) p).1
          ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places) p).2)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [direct_source_frame_coefficient_diagonal, Matrix.diagonal_mul_diagonal]
    simp only [mul_inv_cancel₀ (SourceFrameComponents.CM.direct_source_frame_scale_ne_zero K Q _ _), Matrix.diagonal_one]
  rw [IntrinsicKernelSumTensor.CM.sumComparisonDualCoordinates, hi, Matrix.diagonal_transpose, Matrix.mulVec_diagonal]
  rw [(SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places).apply_symm_apply]

theorem sum_comparison_dual_slot (a : Fin 2 × Fin 2) :
    IntrinsicKernelSumTensor.CM.sumComparisonDualCoordinates K d Q (TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K places a) =
      (SingleIntrinsicCotangentSlots.CM.singleNativeCotangentScale K Q a.2)⁻¹ • Pi.single
        (RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic.slot (A := IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ) a.1 a.2) 1 := by
  funext p
  rw [sum_comparison_dual_apply]
  let e := SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places
  let q : Fin places.count × (Fin 3 × Fin 2) := (places.distinguished, a.1.succ, a.2)
  change (SourceFrameComponents.CM.directSourceFrameScale K Q p.1 p.2)⁻¹ *
    (Pi.single (e.symm q) 1 : PeriodTotal.CM.TotalPositions K places → ℂ) (e.symm p) =
      (SingleIntrinsicCotangentSlots.CM.singleNativeCotangentScale K Q a.2)⁻¹ *
        (Pi.single q 1 : Fin places.count × (Fin 3 × Fin 2) → ℂ) p
  by_cases hp : p = q
  · subst p
    simp only [Pi.single_eq_same, mul_one]
    exact congrArg Inv.inv (SingleIntrinsicCotangentSlots.CM.single_native_cotangent_scale_slot K Q a.2 a.1)
  · have he : e.symm p ≠ e.symm q := fun h => hp (e.symm.injective h)
    simp only [Pi.single_apply, ite_eq_right he, ite_eq_right hp, mul_zero]

end

/-! The native ThetaKernel order-two projection is exactly the source's twice
alternating coefficient, including the factorial and both multiplicity
scales. The resulting normalization is constant and nonzero. -/

open scoped Classical _root_.NumberField _root_.Matrix _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

theorem two_tensor_smul_pair {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (T : ContinuousMultilinearMap ℂ (fun _ : Fin 2 => V) ℂ)
    (a b : ℂ) (u v : V) : T ![a • u, b • v] = a * b * T ![u, v] := by
  let c : Fin 2 → ℂ := ![a, b]
  have h := T.map_smul_univ c ![u, v]
  have hv : (fun i => c i • (![u, v] i)) = ![a • u, b • v] := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at h
  simpa only [c, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, smul_eq_mul] using h

theorem cancel_two_inverse_scales (a b t s : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a⁻¹ * b⁻¹ * t = s) : t = a * b * s := by
  rw [← h]
  field_simp

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun k v => d k (places.representative v)))
  (hμ : ∀ k, d k (places.representative places.distinguished) = true)
  (N : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData _ _ _ (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ))
  (hN : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification N (IntrinsicKernelArithmetic.CM.directSourceNativeSumFrames K Q))
  (hG : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification N)
  (L : (j : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))
  (hL : ∀ j, (L j).coordinates.a = Q.a j ∧ (L j).coordinates.delta = Q.delta)

def sumComparisonTopConstant (z₀ : B.Domain) : ℂ :=
  SingleIntrinsicCotangentSlots.CM.singleNativeCotangentScale K Q 0 * SingleIntrinsicCotangentSlots.CM.singleNativeCotangentScale K Q 1 *
    KernelSumHalfRatio.CM.sumComparisonHalfRatio K d Q hμ N hN L hL z₀

include hG in
theorem sum_comparison_top_constant_ne_zero (z₀ : B.Domain) :
    sumComparisonTopConstant K d Q hμ N hN L hL z₀ ≠ 0 :=
  mul_ne_zero (mul_ne_zero (SingleIntrinsicCotangentSlots.CM.single_native_cotangent_scale_ne_zero K Q 0)
    (SingleIntrinsicCotangentSlots.CM.single_native_cotangent_scale_ne_zero K Q 1))
    (KernelSumHalfRatio.CM.sum_comparison_half_ratio_ne_zero K d Q hμ N hN hG L hL z₀)

include hG in
theorem sum_comparison_native_tensor_slot (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K places))
    (z₀ z : B.Domain) (a b : Fin 2 × Fin 2) :
    RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor N (IntrinsicKernelSum.CM.sumComparisonFiniteInput K Q hμ N hN (fun j => (L j).coordinates) hL φ)
      2 (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
      ![Pi.single (RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic.slot (A := IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ) a.1 a.2) 1,
        Pi.single (RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic.slot (A := IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ) b.1 b.2) 1] =
      SingleIntrinsicCotangentSlots.CM.singleNativeCotangentScale K Q a.2 * SingleIntrinsicCotangentSlots.CM.singleNativeCotangentScale K Q b.2 *
        ((2 : ℂ)⁻¹ * KernelSumHalfRatio.CM.sumComparisonHalfRatio K d Q hμ N hN L hL z₀ *
          InitialTensor.CM.splitThetaTensor K (L 0) (L 1) φ z.val a b) := by
  let T := RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor N
    (IntrinsicKernelSum.CM.sumComparisonFiniteInput K Q hμ N hN (fun j => (L j).coordinates) hL φ)
    2 (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
  have ha := sum_comparison_dual_slot K d Q hμ a
  have hb := sum_comparison_dual_slot K d Q hμ b
  have he := congrArg₂ (fun u v => T ![u, v]) ha hb
  have hm := two_tensor_smul_pair T (SingleIntrinsicCotangentSlots.CM.singleNativeCotangentScale K Q a.2)⁻¹
    (SingleIntrinsicCotangentSlots.CM.singleNativeCotangentScale K Q b.2)⁻¹
    (Pi.single (RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic.slot (A := IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ) a.1 a.2) 1)
    (Pi.single (RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic.slot (A := IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ) b.1 b.2) 1)
  have hs := IntrinsicKernelSumTensor.CM.sum_comparison_geometric_source_slots K d Q hμ N hN hG L hL φ z₀ z a b
  exact cancel_two_inverse_scales _ _ _ _
    (SingleIntrinsicCotangentSlots.CM.single_native_cotangent_scale_ne_zero K Q a.2)
    (SingleIntrinsicCotangentSlots.CM.single_native_cotangent_scale_ne_zero K Q b.2) ((he.trans hm).symm.trans hs)

include hG in
theorem sum_comparison_native_top (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K places)) (z₀ z : B.Domain) :
    RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic.thetaTopForm N (IntrinsicKernelSum.CM.sumComparisonFiniteInput K Q hμ N hN (fun j => (L j).coordinates) hL φ)
      (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) =
        (sumComparisonTopConstant K d Q hμ N hN L hL z₀ *
          InitialTensor.CM.splitThetaTopCoefficient K (L 0) (L 1) φ z.val) • RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic.area := by
  let T := RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor N
    (IntrinsicKernelSum.CM.sumComparisonFiniteInput K Q hμ N hN (fun j => (L j).coordinates) hL φ)
    2 (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
  have hslots (i j : Fin 2) : RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic.slotEmbedding (A := IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ) j
      (if i = 0 then ![1, 0] else ![0, 1]) =
        Pi.single (RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic.slot (A := IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ) i j) 1 := by
    fin_cases i <;> simp [RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic.slotEmbedding]
  have ht : RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic.secondCoefficient T = sumComparisonTopConstant K d Q hμ N hN L hL z₀ *
      InitialTensor.CM.splitThetaTopCoefficient K (L 0) (L 1) φ z.val := by
    change T ![RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic.slotEmbedding 0 ![1, 0], RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic.slotEmbedding 1 ![0, 1]] -
      T ![RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic.slotEmbedding 0 ![0, 1], RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic.slotEmbedding 1 ![1, 0]] -
      T ![RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic.slotEmbedding 1 ![1, 0], RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic.slotEmbedding 0 ![0, 1]] +
      T ![RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic.slotEmbedding 1 ![0, 1], RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic.slotEmbedding 0 ![1, 0]] = _
    have h0 (j : Fin 2) := hslots 0 j
    have h1 (j : Fin 2) := hslots 1 j
    simp only [Fin.isValue, ite_true, one_ne_zero, ite_false] at h0 h1
    rw [h0, h1, h0, h1]
    change RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor N _ 2 _ _ - RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor N _ 2 _ _ -
      RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor N _ 2 _ _ + RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor N _ 2 _ _ = _
    rw [sum_comparison_native_tensor_slot K d Q hμ N hN hG L hL φ z₀ z (0, 0) (1, 1),
      sum_comparison_native_tensor_slot K d Q hμ N hN hG L hL φ z₀ z (1, 0) (0, 1),
      sum_comparison_native_tensor_slot K d Q hμ N hN hG L hL φ z₀ z (0, 1) (1, 0),
      sum_comparison_native_tensor_slot K d Q hμ N hN hG L hL φ z₀ z (1, 1) (0, 0)]
    dsimp only [sumComparisonTopConstant, InitialTensor.CM.splitThetaTopCoefficient, RepresentationTheory.Theta.Kernel.Calculus.doubleAlt]
    ring
  exact congrArg (fun c : ℂ => c • RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic.area) ht

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumSlots.CM
