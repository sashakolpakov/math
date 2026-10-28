import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceScales
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalBallCoordinates
import OAI.RepresentationTheory.Theta.Adelic.GeometricGroup
import OAI.RepresentationTheory.Theta.Adelic.BallNatural

/-! # Source Intrinsic Line -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicLine.CM

noncomputable section

section

/-! The native rational special-unitary action is the original source
matrix at every CM embedding, conjugated by the explicit Hermitian
normalizer. In particular the active matrix uses the original action. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.GeometricGroup

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true)
  (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)
  (N : ℕ) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel N g)

theorem direct_source_rational_local_matrix (v : Fin places.count) :
    ((RepresentationTheory.Theta.Adelic.RationalSU.rationalArchimedeanSU (maximalRealSubfield K)
      (CMGlobalFrames.CM.cmHermitianUnit K Q.delta Q.delta_imaginary B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B))
      (RationalBallUnitary.CM.rationalBallSU K Q.delta Q.delta_imaginary Q.delta_ne_zero B N g hg))
      (RealPlaces.CM.sourceRealPlaces K places v)).val.val.map
        (CMArchimedeanCoordinates.CM.sourceComplexCoordinate K places Q.delta Q.delta_imaginary Q.delta_ne_zero v) =
      (LinearMap.toMatrix' g.toLinearMap).map (HeckeCycles.ReferenceDatum.CM.embeddings K places v) := by
  ext i j
  change CMArchimedeanCoordinates.CM.sourceComplexCoordinate K places Q.delta Q.delta_imaginary Q.delta_ne_zero v
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K Q.delta Q.delta_imaginary)
      (.inl (RealPlaces.CM.sourceRealPlaces K places v))
      ((RationalBallUnitary.CM.rationalBallUnit K Q.delta Q.delta_imaginary Q.delta_ne_zero g).val i j)) = _
  refine (congrArg (fun x => CMArchimedeanCoordinates.CM.sourceComplexCoordinate K places Q.delta Q.delta_imaginary Q.delta_ne_zero v
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K Q.delta Q.delta_imaginary)
      (.inl (RealPlaces.CM.sourceRealPlaces K places v)) x))
    (RationalBallCoordinates.CM.rational_ball_unit_entry K Q.delta Q.delta_imaginary Q.delta_ne_zero g i j)).trans ?_
  exact (CMArchimedeanCoordinates.CM.source_complex_coordinate_rational K places Q.delta Q.delta_imaginary Q.delta_ne_zero v _).trans
    (congrArg (HeckeCycles.ReferenceDatum.CM.embeddings K places v)
      ((QuadraticModel.CM.cmQuadraticEquiv K Q.delta Q.delta_imaginary Q.delta_ne_zero).apply_symm_apply _))

theorem direct_source_standard_matrix (v : Fin places.count) :
    RepresentationTheory.Theta.Adelic.BallGeometryData.standardMatrix (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother)
      (RepresentationTheory.Theta.Adelic.RationalSU.rationalArchimedeanSU (maximalRealSubfield K)
        (CMGlobalFrames.CM.cmHermitianUnit K Q.delta Q.delta_imaginary B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B))
        (RationalBallUnitary.CM.rationalBallSU K Q.delta Q.delta_imaginary Q.delta_ne_zero B N g hg)) v =
      ((BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother).basisV v).inv *
        (LinearMap.toMatrix' g.toLinearMap).map (HeckeCycles.ReferenceDatum.CM.embeddings K places v) *
          ((BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother).basisV v).val := by
  exact congrArg (fun M => ((BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother).basisV v).inv * M *
    ((BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother).basisV v).val)
    (direct_source_rational_local_matrix K Q N g hg v)

theorem direct_source_active_standard_matrix :
    RepresentationTheory.Theta.Adelic.BallGeometryData.standardMatrix (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother)
      (RepresentationTheory.Theta.Adelic.RationalSU.rationalArchimedeanSU (maximalRealSubfield K)
        (CMGlobalFrames.CM.cmHermitianUnit K Q.delta Q.delta_imaginary B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B))
        (RationalBallUnitary.CM.rationalBallSU K Q.delta Q.delta_imaginary Q.delta_ne_zero B N g hg)) places.distinguished =
      ((BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother).basisV places.distinguished).inv *
        BallActionMatrix.CM.ballActionMatrix K g *
          ((BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother).basisV places.distinguished).val := by
  have hm : (LinearMap.toMatrix' g.toLinearMap).map (HeckeCycles.ReferenceDatum.CM.embeddings K places places.distinguished) =
      BallActionMatrix.CM.ballActionMatrix K g := by
    ext i j
    exact congrArg (fun f => f (LinearMap.toMatrix' g.toLinearMap i j)) (HeckeCycles.ReferenceDatum.CM.embeddings_distinguished K places)
  exact (direct_source_standard_matrix K Q hμ hother N g hg places.distinguished).trans
    (congrArg (fun M => ((BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother).basisV places.distinguished).inv * M *
      ((BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother).basisV places.distinguished).val) hm)

end

section

/-! The active Hermitian normalizer rescales precisely the third
homogeneous coordinate. Its conjugation preserves the source projective
denominator and rescales the affine ball coordinates by the same radius. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.RationalSU

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

def weightedBallConjugate (r : ℂ) (M : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (fun i => if i = 2 then r else 1) * M *
    Matrix.diagonal (fun i => if i = 2 then r⁻¹ else 1)

theorem weighted_ball_conjugate_line (r : ℂ) (hr : r ≠ 0)
    (M : Matrix (Fin 3) (Fin 3) ℂ) (z : HeckeCycles.GeometricSource.CM.BallChart) :
    (weightedBallConjugate r M).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector (fun j => z j / r)) =
      fun i => if i = 2 then M.mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z) i
        else M.mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z) i / r := by
  funext i
  fin_cases i <;>
    simp [weightedBallConjugate, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, HeckeCycles.GeometricSource.CM.BallDatum.lineVector] <;>
    field_simp [hr]

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true)
  (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)

theorem direct_source_active_basis_inverse :
    ((BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother).basisV places.distinguished).inv =
      Matrix.diagonal (fun i => if i = 2 then (SourceIntrinsicBall.CM.sourceBallRadius K B : ℂ) else 1) := by
  have h := SourceScales.CM.source_hermitian_normalizer_inv K places B.b B.conjugate_b
    (BallArithmetic.CM.direct_source_ball_b_ne_zero K B) places.distinguished
  have hs : (fun i : Fin 3 => if i = 2 then (SourceScales.CM.sourceNativePlaceRadius K places B.b places.distinguished : ℂ) else 1) =
      (fun i : Fin 3 => if i = 2 then (SourceIntrinsicBall.CM.sourceBallRadius K B : ℂ) else 1) := by
    rw [SourceScales.CM.source_native_place_radius_active]
  exact h.trans (congrArg Matrix.diagonal hs)

theorem direct_source_active_basis_value :
    ((BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother).basisV places.distinguished).val =
      Matrix.diagonal (fun i => if i = 2 then (SourceIntrinsicBall.CM.sourceBallRadius K B : ℂ)⁻¹ else 1) := by
  change Matrix.diagonal (fun i => (DiagonalNormalization.CM.diagonalNormalizationScale
    (CMFormCoordinates.CM.sourceHermitianRealCoefficients K places B.b places.distinguished i) : ℂ)) = _
  apply congrArg Matrix.diagonal
  funext i
  by_cases hi : i = 2
  · subst i
    change (((Real.sqrt |(HeckeCycles.ReferenceDatum.CM.embeddings K places places.distinguished B.b).re|)⁻¹ : ℝ) : ℂ) =
      (SourceIntrinsicBall.CM.sourceBallRadius K B : ℂ)⁻¹
    rw [Complex.ofReal_inv]
    exact congrArg (fun r : ℝ => (r : ℂ)⁻¹) (SourceScales.CM.source_native_place_radius_active K places B)
  · simp [DiagonalNormalization.CM.diagonalNormalizationScale, CMFormCoordinates.CM.sourceHermitianRealCoefficients, hi]

variable (N : ℕ) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel N g)

theorem direct_source_active_matrix_weighted :
    RepresentationTheory.Theta.Adelic.BallGeometryData.standardMatrix (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother)
      (RepresentationTheory.Theta.Adelic.RationalSU.rationalArchimedeanSU (maximalRealSubfield K)
        (CMGlobalFrames.CM.cmHermitianUnit K Q.delta Q.delta_imaginary B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B))
        (RationalBallUnitary.CM.rationalBallSU K Q.delta Q.delta_imaginary Q.delta_ne_zero B N g hg)) places.distinguished =
      weightedBallConjugate (SourceIntrinsicBall.CM.sourceBallRadius K B : ℂ) (BallActionMatrix.CM.ballActionMatrix K g) := by
  refine (direct_source_active_standard_matrix K Q hμ hother N g hg).trans ?_
  exact congrArg₂ (fun M P => M * BallActionMatrix.CM.ballActionMatrix K g * P)
    (direct_source_active_basis_inverse K Q hμ hother) (direct_source_active_basis_value K Q hμ hother)

end

/-! The constructed native ball action agrees exactly with the literal
principal action on the original BallDatum, under its radius coordinates.
The natural denominator is the original projective denominator. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.GeometricGroup
open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallNatural.Factors

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true)
  (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)
  (N : ℕ) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel N g)

abbrev directSourceBallGroup : RepresentationTheory.Theta.Adelic.BallNatural.BallGroup :=
  RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother)
    (RepresentationTheory.Theta.Adelic.RationalSU.rationalArchimedeanSU (maximalRealSubfield K)
      (CMGlobalFrames.CM.cmHermitianUnit K Q.delta Q.delta_imaginary B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B))
      (RationalBallUnitary.CM.rationalBallSU K Q.delta Q.delta_imaginary Q.delta_ne_zero B N g hg))

theorem direct_source_ball_group_matrix :
    (RepresentationTheory.Theta.Adelic.BallNatural.asSL (directSourceBallGroup K Q hμ hother N g hg)).val =
      weightedBallConjugate (SourceIntrinsicBall.CM.sourceBallRadius K B : ℂ) (BallActionMatrix.CM.ballActionMatrix K g) :=
  direct_source_active_matrix_weighted K Q hμ hother N g hg

theorem direct_source_native_image_line (z : B.Domain) :
    (RepresentationTheory.Theta.Adelic.BallNatural.asSL (directSourceBallGroup K Q hμ hother N g hg)).val.mulVec
      (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z).val) =
      fun i => if i = 2 then (BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) i
        else (BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) i / (SourceIntrinsicBall.CM.sourceBallRadius K B : ℂ) := by
  have hm := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ =>
    M.mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector (fun j => z.val j / (SourceIntrinsicBall.CM.sourceBallRadius K B : ℂ))))
    (direct_source_ball_group_matrix K Q hμ hother N g hg)
  exact hm.trans (weighted_ball_conjugate_line (SourceIntrinsicBall.CM.sourceBallRadius K B : ℂ)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (SourceIntrinsicBall.CM.source_ball_radius_pos K B))) (BallActionMatrix.CM.ballActionMatrix K g) z.val)

theorem direct_source_native_denominator (z : B.Domain) :
    RepresentationTheory.Theta.Adelic.BallNatural.Factors.automorphyFactor (directSourceBallGroup K Q hμ hother N g hg) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) =
      (BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2 := by
  have h := congrFun (direct_source_native_image_line K Q hμ hother N g hg z) 2
  simpa only [ite_true] using! h

theorem source_native_principal_ball_action (z : B.Domain) :
    directSourceBallGroup K Q hμ hother N g hg • SourceIntrinsicBall.CM.sourceNativeBallPoint K B z =
      SourceIntrinsicBall.CM.sourceNativeBallPoint K B (BallLineAction.CM.ballPrincipalAction K B g hg.1 z) := by
  apply Subtype.ext
  funext j
  have ht := congrFun (direct_source_native_image_line K Q hμ hother N g hg z) j.castSucc
  have hj : j.castSucc ≠ (2 : Fin 3) := Fin.castSucc_ne_last j
  simp only [ite_eq_right hj] at ht
  have hb := direct_source_native_denominator K Q hμ hother N g hg z
  change ((RepresentationTheory.Theta.Adelic.BallNatural.asSL (directSourceBallGroup K Q hμ hother N g hg)).val.mulVec
      (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z).val) j.castSucc) /
      RepresentationTheory.Theta.Adelic.BallNatural.Factors.automorphyFactor (directSourceBallGroup K Q hμ hother N g hg) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) =
    ((BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) j.castSucc /
      (BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2) / (SourceIntrinsicBall.CM.sourceBallRadius K B : ℂ)
  rw [ht, hb]
  ring

theorem source_native_natural_half_factor (z : B.Domain) :
    RepresentationTheory.Theta.Adelic.BallNatural.Factors.naturalHalfFactor 2 (directSourceBallGroup K Q hμ hother N g hg) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) =
      ((BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2) ^ 2 :=
  congrArg (fun c : ℂ => c ^ 2) (direct_source_native_denominator K Q hμ hother N g hg z)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicLine.CM
