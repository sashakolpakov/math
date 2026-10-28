import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactFrameComparison
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactRealPhase
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicImaginaryComparison

/-! # Intrinsic Compact Zero -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.IntrinsicCompactZero.IntrinsicImaginary

/-! The compact-action chart has the positive imaginary quadratic
form obtained by pulling back the actual native period along its real
rational position change. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactPhaseChange.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactSymplecticTransport.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactActionParameter.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactFrameComparison.IntrinsicGraph OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactRealPhase.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicImaginaryComparison.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}
variable (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (B : Adelic.DataTheta.ComparisonData F H K A)
variable (Bp : Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}

theorem compact_imaginary_bilinear (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (z : Adelic.BallNatural.Ball) (x y : Adelic.BallGeometryData.FrameIndex A → ℝ) :
    ((IntrinsicCompactRealPhase.Intrinsic.compactRealPositionMatrix p B Bp).mulVec x) ⬝ᵥ
        ((IntrinsicImaginaryComparison.Intrinsic.realImaginary (Bp.period z).matrix).mulVec ((IntrinsicCompactRealPhase.Intrinsic.compactRealPositionMatrix p B Bp).mulVec y)) =
      x ⬝ᵥ ((IntrinsicImaginaryComparison.Intrinsic.realImaginary (IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))).mulVec y) := by
  have h := IntrinsicImaginaryComparison.Intrinsic.cross_graph_difference (IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp).toLinearMap
    (IntrinsicCompactSymplecticTransport.Intrinsic.compactPositionLinear p B Bp) (IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)) (Bp.period z).matrix
    (IntrinsicCompactSymplecticTransport.Intrinsic.compact_phase_pairing p B Bp hC hCp) (IntrinsicCompactSymplecticTransport.Intrinsic.compact_phase_positions p B Bp hC hCp)
    (IntrinsicCompactFrameComparison.IntrinsicGraph.compact_graph_in_positions p B Bp hC hCp hG hGp z)
    (fun i => (x i : ℂ)) (fun i => (y i : ℂ))
  erw [IntrinsicCompactRealPhase.Intrinsic.compact_position_real p B Bp hC hCp x,IntrinsicCompactRealPhase.Intrinsic.compact_position_real p B Bp hC hCp y] at h
  have he := IntrinsicCompactRealPhase.Intrinsic.compact_phase_change_real p B Bp hC hCp (Sum.elim x (0 : Adelic.BallGeometryData.FrameIndex A → ℝ))
  have hc : (fun i => ((Sum.elim x (0 : Adelic.BallGeometryData.FrameIndex A → ℝ)) i : ℂ)) =
      Sum.elim (fun i => (x i : ℂ)) (0 : Adelic.BallGeometryData.FrameIndex A → ℂ) := by
    funext i
    cases i <;> simp only [Sum.elim_inl,Sum.elim_inr,Pi.zero_apply,Complex.ofReal_zero]
  rw [hc] at he
  erw [he] at h
  have hi := congrArg Complex.im h
  erw [Complex.sub_im,IntrinsicImaginaryComparison.Intrinsic.complex_bilinear_im,IntrinsicImaginaryComparison.Intrinsic.complex_bilinear_im] at hi
  have hz : (∑ j,
      (IntrinsicCompactRealPhase.Intrinsic.compactRealPhaseChange p B Bp (Sum.elim x (0 : Adelic.BallGeometryData.FrameIndex A → ℝ)) (.inr j) : ℂ) *
        ((IntrinsicCompactRealPhase.Intrinsic.compactRealPositionMatrix p B Bp).mulVec y j : ℂ)).im = 0 := by simp
  erw [hz] at hi
  exact sub_eq_zero.mp hi

theorem compact_real_position_injective : Function.Injective (IntrinsicCompactRealPhase.Intrinsic.compactRealPositionMatrix p B Bp).mulVec := by
  intro x y h
  have he := congrArg (IntrinsicCompactRealPhase.Intrinsic.compactRealPositionInverse p B Bp).mulVec h
  simpa only [Matrix.mulVec_mulVec,IntrinsicCompactRealPhase.Intrinsic.compact_real_position_inverse,Matrix.one_mulVec] using he

theorem compact_imaginary_quadratic_positive (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (z : Adelic.BallNatural.Ball) (x : Adelic.BallGeometryData.FrameIndex A → ℝ) (hx : x ≠ 0) :
    0 < x ⬝ᵥ ((IntrinsicImaginaryComparison.Intrinsic.realImaginary (IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))).mulVec x) := by
  have hzero : (IntrinsicCompactRealPhase.Intrinsic.compactRealPositionMatrix p B Bp).mulVec x ≠ 0 := by
    intro hz
    apply hx
    exact compact_real_position_injective p B Bp (hz.trans (Matrix.mulVec_zero _).symm)
  have hp := (Bp.period z).imaginary_posDef.dotProduct_mulVec_pos hzero
  have he := compact_imaginary_bilinear p B Bp hC hCp hG hGp z x x
  exact he ▸ hp

end RepresentationTheory.Theta.Kernel.IntrinsicCompactZero.IntrinsicImaginary

namespace RepresentationTheory.Theta.Kernel.IntrinsicCompactZero.IntrinsicPositivePeriod

/-! The actual compact-action chart has a symmetric period with
positive imaginary part. Both properties follow from the native period
under the proved real symplectic coordinate comparison. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactPhaseChange.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactSymplecticTransport.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactActionParameter.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactFrameComparison.IntrinsicGraph OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactZero.IntrinsicImaginary
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicImaginaryComparison.Intrinsic

theorem graph_pairing_zero {I : Type} [Fintype I] (Z : Matrix I I ℂ) (hZ : Z.IsSymm)
    (x y : I → ℂ) : Adelic.DataTheta.standardPairing (Sum.elim x (Z.mulVec x)) (Sum.elim y (Z.mulVec y)) = 0 := by
  change (∑ i, (x i * Z.mulVec y i - Z.mulVec x i * y i)) = 0
  rw [Finset.sum_sub_distrib]
  change x ⬝ᵥ Z.mulVec y - Z.mulVec x ⬝ᵥ y = 0
  rw [dotProduct_comm (Z.mulVec x) y]
  exact sub_eq_zero.mpr (by simpa only [hZ.eq] using Matrix.dotProduct_transpose_mulVec Z x y)

theorem symmetric_of_graph_isotropic {I : Type} [Fintype I] [DecidableEq I]
    (Z : Matrix I I ℂ)
    (h : ∀ x y, Adelic.DataTheta.standardPairing (Sum.elim x (Z.mulVec x)) (Sum.elim y (Z.mulVec y)) = 0) : Z.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  have he : Z i j - Z j i = 0 := by
    have hh := h (Pi.single i 1) (Pi.single j 1)
    simp only [Adelic.DataTheta.standardPairing,Sum.elim_inl,Sum.elim_inr,Finset.sum_sub_distrib] at hh
    change (Pi.single i (1 : ℂ)) ⬝ᵥ Z.mulVec (Pi.single j 1) -
      Z.mulVec (Pi.single i 1) ⬝ᵥ (Pi.single j 1) = 0 at hh
    rw [single_one_dotProduct,dotProduct_single_one,Matrix.mulVec_single_one,Matrix.mulVec_single_one] at hh
    exact hh
  exact (sub_eq_zero.mp he).symm

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}
variable (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (B : Adelic.DataTheta.ComparisonData F H K A)
variable (Bp : Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}

theorem compact_chart_symmetric (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (z : Adelic.BallNatural.Ball) :
    (IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).IsSymm := by
  apply symmetric_of_graph_isotropic
  intro x y
  have hx := IntrinsicCompactFrameComparison.IntrinsicGraph.compact_graph_in_positions p B Bp hC hCp hG hGp z x
  have hy := IntrinsicCompactFrameComparison.IntrinsicGraph.compact_graph_in_positions p B Bp hC hCp hG hGp z y
  have hpair := IntrinsicCompactSymplecticTransport.Intrinsic.compact_phase_pairing p B Bp hC hCp
    (Sum.elim x ((IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).mulVec x))
    (Sum.elim y ((IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).mulVec y))
  exact hpair.symm.trans ((congrArg₂ Adelic.DataTheta.standardPairing hx hy).trans
    (graph_pairing_zero (Bp.period z).matrix (Bp.period z).symmetric
      (IntrinsicCompactSymplecticTransport.Intrinsic.compactPositionLinear p B Bp x) (IntrinsicCompactSymplecticTransport.Intrinsic.compactPositionLinear p B Bp y)))

theorem compact_chart_imaginary_positive (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (z : Adelic.BallNatural.Ball) :
    (IntrinsicImaginaryComparison.Intrinsic.realImaginary (IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨Matrix.isHermitian_iff_isSymm.mpr
    ((compact_chart_symmetric p B Bp hC hCp hG hGp z).map Complex.im),?_⟩
  intro x hx
  simpa only [star_trivial] using IntrinsicImaginary.compact_imaginary_quadratic_positive p B Bp hC hCp hG hGp z x hx

def compactActionSiegel (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (z : Adelic.BallNatural.Ball) : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A) :=
  ⟨IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val),compact_chart_symmetric p B Bp hC hCp hG hGp z,
    compact_chart_imaginary_positive p B Bp hC hCp hG hGp z⟩

end RepresentationTheory.Theta.Kernel.IntrinsicCompactZero.IntrinsicPositivePeriod

namespace RepresentationTheory.Theta.Kernel.IntrinsicCompactZero.IntrinsicCompletion

/-! The actual compact-coordinate comparison transports the inverse
imaginary form, Jacobi frame, and theta completion factor exactly. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactActionParameter.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactFrameComparison.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactPositionMatrices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactRealPhase.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactZero.IntrinsicImaginary
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactZero.IntrinsicPositivePeriod OAI.RepresentationTheory.Theta.Kernel.IntrinsicImaginaryComparison.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicInversePullback.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.IntrinsicHalfFrame

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}
variable (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (B : Adelic.DataTheta.ComparisonData F H K A)
variable (Bp : Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}

theorem compact_imaginary_congruence (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (z : Adelic.BallNatural.Ball) :
    (IntrinsicCompactPositionMatrices.Intrinsic.compactPositionMatrix p B Bp)ᵀ *
      (AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary (Bp.period z).matrix : Matrix (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A) ℂ) *
      IntrinsicCompactPositionMatrices.Intrinsic.compactPositionMatrix p B Bp = AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary (IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)) := by
  have h := IntrinsicImaginaryComparison.Intrinsic.congruence_of_bilinear (IntrinsicCompactRealPhase.Intrinsic.compactRealPositionMatrix p B Bp)
    (IntrinsicImaginaryComparison.Intrinsic.realImaginary (IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)))
    (IntrinsicImaginaryComparison.Intrinsic.realImaginary (Bp.period z).matrix) (IntrinsicImaginary.compact_imaginary_bilinear p B Bp hC hCp hG hGp z)
  have hc := congrArg (fun M => M.map Complex.ofRealHom) h
  rw [Matrix.map_mul,Matrix.map_mul,Matrix.transpose_map] at hc
  simp only [← IntrinsicCompactRealPhase.Intrinsic.compact_position_matrix_real] at hc
  exact hc

theorem compact_imaginary_inverse (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (z : Adelic.BallNatural.Ball) :
    (AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary (Bp.period z).matrix)⁻¹ = IntrinsicCompactPositionMatrices.Intrinsic.compactPositionMatrix p B Bp *
      (AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary (IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)))⁻¹ *
        (IntrinsicCompactPositionMatrices.Intrinsic.compactPositionMatrix p B Bp)ᵀ :=
  IntrinsicInversePullback.Intrinsic.inverse_congruence (I := Adelic.BallGeometryData.FrameIndex A) (J := Adelic.BallGeometryData.FrameIndex A)
    _ (IntrinsicCompactPositionMatrices.Intrinsic.compactPositionInverse p B Bp) _ _ (IntrinsicCompactPositionMatrices.Intrinsic.compact_position_matrix_inverse p B Bp)
    (IntrinsicPositivePeriod.compactActionSiegel p B Bp hC hCp hG hGp z).matrixImaginary_det_isUnit
    (Bp.period z).matrixImaginary_det_isUnit (compact_imaginary_congruence p B Bp hC hCp hG hGp z)

theorem compact_jacobi_relation (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (z : Adelic.BallNatural.Ball) (u : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    ((IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))⁻¹ᵀ).mulVec u =
      (IntrinsicCompactPositionMatrices.Intrinsic.compactPositionMatrix p B Bp)ᵀ.mulVec ((Bp.frame z).invᵀ.mulVec u) := by
  let N : (Matrix (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A) ℂ)ˣ := Bp.frame z
  have hf : IntrinsicCompactPositionMatrices.Intrinsic.compactPositionMatrix p B Bp * IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val) = N.val :=
    IntrinsicCompactFrameComparison.Intrinsic.compact_position_frame p B Bp hC hCp hG hGp z
  have hleft : (N.inv * IntrinsicCompactPositionMatrices.Intrinsic.compactPositionMatrix p B Bp) *
      IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val) = 1 := by
    rw [Matrix.mul_assoc,hf,N.inv_val]
  change ((IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))⁻¹ᵀ).mulVec u =
    (IntrinsicCompactPositionMatrices.Intrinsic.compactPositionMatrix p B Bp)ᵀ.mulVec (N.invᵀ.mulVec u)
  rw [Matrix.inv_eq_left_inv hleft,Matrix.transpose_mul,← Matrix.mulVec_mulVec]

theorem compact_completion_comparison (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (z : Adelic.BallNatural.Ball) (u : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor (((Real.pi : ℂ) / 2) •
      AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear ((AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary (Bp.period z).matrix)⁻¹)) ((Bp.frame z).invᵀ.mulVec u) =
      AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor (((Real.pi : ℂ) / 2) •
        AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear ((AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary (IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)))⁻¹))
          (((IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))⁻¹ᵀ).mulVec u) := by
  have h := IntrinsicInversePullback.Intrinsic.inverse_quadratic_pullback (IntrinsicCompactPositionMatrices.Intrinsic.compactPositionMatrix p B Bp) _ _
    (compact_imaginary_inverse p B Bp hC hCp hG hGp z) ((Bp.frame z).invᵀ.mulVec u)
  erw [← compact_jacobi_relation p B Bp hC hCp hG hGp z u] at h
  simp only [AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor,_root_.smul_apply,AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear_apply,smul_eq_mul]
  exact congrArg (fun t : ℂ => Complex.exp (((Real.pi : ℂ) / 2) * t)) h

end RepresentationTheory.Theta.Kernel.IntrinsicCompactZero.IntrinsicCompletion

end

end OAI
