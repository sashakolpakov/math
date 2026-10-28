import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneComplexComponents
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneFrameComparison

/-! # One Frame Determinant -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneFrameDeterminant

noncomputable section

section

/-! Equality of the AdelicTheta period with the actual native Siegel period,
derived from their common geometric Hodge frame. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta

namespace Quadratic

def comparisonFrameCoordinates
    {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
    {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
    {K : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
    {A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H K} (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H K A)
    (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (a : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ := (B.frame z).val.mulVec a

def singleMatrixReindex (n : ℕ)
    (M : Matrix (Fin n × (Fin 3 × Fin 1)) (Fin n × (Fin 3 × Fin 1)) ℂ) :
    Matrix (Fin n × Fin 3) (Fin n × Fin 3) ℂ :=
  fun i j => M (Multiplicity.OneIndex.Quadratic.singleFrameIndex n i) (Multiplicity.OneIndex.Quadratic.singleFrameIndex n j)

theorem singleMatrixReindex_mulVec (n : ℕ)
    (M : Matrix (Fin n × (Fin 3 × Fin 1)) (Fin n × (Fin 3 × Fin 1)) ℂ)
    (u : Fin n × Fin 3 → ℂ) (i : Fin n × Fin 3) :
    (singleMatrixReindex n M).mulVec u i =
      M.mulVec (fun j => u ((Multiplicity.OneIndex.Quadratic.singleFrameIndex n).symm j)) (Multiplicity.OneIndex.Quadratic.singleFrameIndex n i) := by
  simpa only [Matrix.mulVec, dotProduct, singleMatrixReindex, Equiv.symm_apply_apply] using
    (Multiplicity.OneIndex.Quadratic.singleFrameIndex n).sum_comp
      (fun j => M (Multiplicity.OneIndex.Quadratic.singleFrameIndex n i) j * u ((Multiplicity.OneIndex.Quadratic.singleFrameIndex n).symm j))

theorem singleGraph_relation (n : ℕ)
    (M : Matrix (Fin n × (Fin 3 × Fin 1)) (Fin n × (Fin 3 × Fin 1)) ℂ)
    (a b : Fin n × Fin 3 → ℂ) (t : Fin n × (Fin 3 × Fin 1) → ℂ)
    (h : RepresentationTheory.Theta.Adelic.DataTheta.swapPhase ((OneComplexComponents.Quadratic.singleComplexPhaseReindex n).symm (Sum.elim a b)) =
      Sum.elim t (M.mulVec t)) :
    (singleMatrixReindex n M).mulVec b = a := by
  have hb : (fun j => b ((Multiplicity.OneIndex.Quadratic.singleFrameIndex n).symm j)) = t := by
    funext j
    exact congrFun h (.inl j)
  funext i
  rw [singleMatrixReindex_mulVec, hb]
  exact (congrFun h (.inr (Multiplicity.OneIndex.Quadratic.singleFrameIndex n i))).symm

end Quadratic

namespace Multiplicity

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (hs : 2 ≤ s) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP)
    (Intrinsic.OneTheta.Multiplicity.nativeOneSkew E P hP v) (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv))

def nativeOnePhaseInput (w : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) :
    (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv) ⊕
      RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv)) → ℂ :=
  RepresentationTheory.Theta.Adelic.DataTheta.swapPhase ((OneComplexComponents.Quadratic.singleComplexPhaseReindex s).symm
    (RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates E P.embeddings hP.1
      (Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B) w))

theorem nativeOneComplexCoordinates_phase (w : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) :
    OneComplexComponents.Multiplicity.nativeOneComplexCoordinates E P hP hμ hs v hv B w =
      B.complexPhase (nativeOnePhaseInput E P hP hμ hs v hv B w) := rfl

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

theorem nativeOne_period_columns
    (hCoord : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification B (Intrinsic.OneTheta.Multiplicity.nativeOneFrames E P hP v))
    (hGeometry : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification B) (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    Quadratic.singleMatrixReindex s (B.period (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ z)).matrix *
      Multiplicity.Period.nativeLowerFrame E P hP v (Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B) z.val =
        Multiplicity.Period.nativeUpperFrame E P hP v (Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B) z.val := by
  let e := Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B
  let ec := RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates E P.embeddings hP.1 e
  let fr := RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.flatFrame (Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Intrinsic.Multiplicity.nativeMatrix E P)) P.distinguished
    (Multiplicity.Period.nativeCompactSigns E P v) z.val
  let p := OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ z
  apply Matrix.ext_iff_mulVec.mpr
  intro u
  rw [← Matrix.mulVec_mulVec]
  have h := (OneComplexComponents.Multiplicity.nativeOneComplexCoordinates_components E P hP hμ hs v hv B hCoord (fr u)).trans
    (OneFrameComparison.Multiplicity.nativeOne_geometricFrame E P hP hμ hs v hv z u)
  have hg := hGeometry.2.2.2.2.2.2.1 p (OneFrameComparison.Multiplicity.nativeOneFrameCoefficients E P hP hμ hs v hv u)
  have hphase : RepresentationTheory.Theta.Adelic.DataTheta.swapPhase ((OneComplexComponents.Quadratic.singleComplexPhaseReindex s).symm (ec (fr u))) =
      Sum.elim (Quadratic.comparisonFrameCoordinates B p (OneFrameComparison.Multiplicity.nativeOneFrameCoefficients E P hP hμ hs v hv u))
        ((B.period p).matrix.mulVec
          (Quadratic.comparisonFrameCoordinates B p (OneFrameComparison.Multiplicity.nativeOneFrameCoefficients E P hP hμ hs v hv u))) := by
    have hh := (nativeOneComplexCoordinates_phase E P hP hμ hs v hv B (fr u)).symm.trans
      (h.trans hg.symm)
    have hc := B.complexPhase.injective hh
    have hec : nativeOnePhaseInput E P hP hμ hs v hv B (fr u) =
        RepresentationTheory.Theta.Adelic.DataTheta.swapPhase ((OneComplexComponents.Quadratic.singleComplexPhaseReindex s).symm (ec (fr u))) := rfl
    exact hec.symm.trans hc
  have hblocks : ec (fr u) = Sum.elim
      ((Multiplicity.Period.nativeUpperFrame E P hP v e z.val).mulVec u)
      ((Multiplicity.Period.nativeLowerFrame E P hP v e z.val).mulVec u) := by
    funext i
    cases i with
    | inl j => exact (congrFun (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.upperFrame_mulVec ec _ _ _ z.val u) j).symm
    | inr j => exact (congrFun (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.lowerFrame_mulVec ec _ _ _ z.val u) j).symm
  exact Quadratic.singleGraph_relation s (B.period p).matrix _ _ _
    ((congrArg (fun w => RepresentationTheory.Theta.Adelic.DataTheta.swapPhase
      ((OneComplexComponents.Quadratic.singleComplexPhaseReindex s).symm w)) hblocks).symm.trans hphase)

theorem nativeOne_period_matrix
    (hCoord : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification B (Intrinsic.OneTheta.Multiplicity.nativeOneFrames E P hP v))
    (hGeometry : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification B) (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    Quadratic.singleMatrixReindex s (B.period (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ z)).matrix =
      (Intrinsic.PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv (Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B)
        (Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates_pairing E P hP hμ hs v hv B hCoord) z).matrix := by
  let e := Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B
  let low := Multiplicity.Period.nativeLowerFrame E P hP v e z.val
  have hdet : IsUnit low.det := isUnit_iff_ne_zero.mpr
    (Intrinsic.PeriodFamily.Multiplicity.native_lowerFrame_det E P hP hμ v hv e
      (Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates_pairing E P hP hμ hs v hv B hCoord) z.val z.property)
  have h := congrArg (fun M : Matrix (Fin s × Fin 3) (Fin s × Fin 3) ℂ => M * low⁻¹)
    (nativeOne_period_columns E P hP hμ hs v hv B hCoord hGeometry z)
  change (_ * low) * low⁻¹ = _ at h
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one] at h
  exact h

end Multiplicity

end

/-! The exact constant determinant relating the AdelicTheta and native frames. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta

namespace Quadratic

def comparisonFrameMatrix
    {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
    {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
    {K : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
    {A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H K} (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H K A)
    (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) : Matrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)
      (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) ℂ := (B.frame z).val

def comparisonFrameDet
    {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
    {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
    {K : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
    {A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H K} (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H K A)
    (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) : ℂ := (B.frame z).val.det

theorem comparisonFrameDeterminant
    {I : Type} [Fintype I] [DecidableEq I]
    {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
    {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
    {K : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
    {A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H K} (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H K A)
    (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (e : I ≃ RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)
    (c : I → ℂ) (L : Matrix I I ℂ)
    (h : (comparisonFrameMatrix B z).submatrix e e * Matrix.diagonal c = L) :
    comparisonFrameDet B z * (∏ i, c i) = L.det := by
  have hd := congrArg Matrix.det h
  simpa only [Matrix.det_mul, Matrix.det_diagonal, Matrix.det_submatrix_equiv_self,
    comparisonFrameDet, comparisonFrameMatrix] using hd

theorem singleMatrixReindex_det (n : ℕ)
    (M : Matrix (Fin n × (Fin 3 × Fin 1)) (Fin n × (Fin 3 × Fin 1)) ℂ) :
    (singleMatrixReindex n M).det = M.det :=
  Matrix.det_submatrix_equiv_self (Multiplicity.OneIndex.Quadratic.singleFrameIndex n) M

theorem singleFrameDeterminant (n : ℕ)
    (M : Matrix (Fin n × (Fin 3 × Fin 1)) (Fin n × (Fin 3 × Fin 1)) ℂ)
    (d : Fin n × Fin 3 → ℂ) (L : Matrix (Fin n × Fin 3) (Fin n × Fin 3) ℂ)
    (h : singleMatrixReindex n M * Matrix.diagonal d = L) :
    M.det * (∏ i, d i) = L.det := by
  have hd := congrArg Matrix.det h
  simpa only [Matrix.det_mul, singleMatrixReindex_det, Matrix.det_diagonal] using hd

end Quadratic

namespace Multiplicity

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (hs : 2 ≤ s) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP)
    (Intrinsic.OneTheta.Multiplicity.nativeOneSkew E P hP v) (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv))

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

theorem nativeOne_lowerFrame_matrix
    (hCoord : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification B (Intrinsic.OneTheta.Multiplicity.nativeOneFrames E P hP v))
    (hGeometry : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification B) (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    Quadratic.singleMatrixReindex s (Quadratic.comparisonFrameMatrix B (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ z)) *
      Matrix.diagonal (fun i : Fin s × Fin 3 => OneComponentScales.Multiplicity.nativeOneFrameScale E P v i.1 i.2) =
        Multiplicity.Period.nativeLowerFrame E P hP v (Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B) z.val := by
  let e := Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B
  let ec := RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates E P.embeddings hP.1 e
  let fr := RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.flatFrame (Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Intrinsic.Multiplicity.nativeMatrix E P)) P.distinguished
    (Multiplicity.Period.nativeCompactSigns E P v) z.val
  let p := OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ z
  apply Matrix.ext_iff_mulVec.mpr
  intro u
  rw [← Matrix.mulVec_mulVec]
  have h := (OneComplexComponents.Multiplicity.nativeOneComplexCoordinates_components E P hP hμ hs v hv B hCoord (fr u)).trans
    (OneFrameComparison.Multiplicity.nativeOne_geometricFrame E P hP hμ hs v hv z u)
  have hg := hGeometry.2.2.2.2.2.2.1 p (OneFrameComparison.Multiplicity.nativeOneFrameCoefficients E P hP hμ hs v hv u)
  have hphase : RepresentationTheory.Theta.Adelic.DataTheta.swapPhase ((OneComplexComponents.Quadratic.singleComplexPhaseReindex s).symm (ec (fr u))) =
      Sum.elim (Quadratic.comparisonFrameCoordinates B p (OneFrameComparison.Multiplicity.nativeOneFrameCoefficients E P hP hμ hs v hv u))
        ((B.period p).matrix.mulVec
          (Quadratic.comparisonFrameCoordinates B p (OneFrameComparison.Multiplicity.nativeOneFrameCoefficients E P hP hμ hs v hv u))) := by
    have hh := (nativeOneComplexCoordinates_phase E P hP hμ hs v hv B (fr u)).symm.trans
      (h.trans hg.symm)
    have hc := B.complexPhase.injective hh
    have hec : nativeOnePhaseInput E P hP hμ hs v hv B (fr u) =
        RepresentationTheory.Theta.Adelic.DataTheta.swapPhase ((OneComplexComponents.Quadratic.singleComplexPhaseReindex s).symm (ec (fr u))) := rfl
    exact hec.symm.trans hc
  have hcoeff : (fun j =>
      (Matrix.diagonal (fun i : Fin s × Fin 3 => OneComponentScales.Multiplicity.nativeOneFrameScale E P v i.1 i.2)).mulVec u
        ((Multiplicity.OneIndex.Quadratic.singleFrameIndex s).symm j)) = OneFrameComparison.Multiplicity.nativeOneFrameCoefficients E P hP hμ hs v hv u := by
    funext j
    simp only [Matrix.mulVec_diagonal]
    rfl
  funext i
  have hr := Quadratic.singleMatrixReindex_mulVec s (Quadratic.comparisonFrameMatrix B p)
    ((Matrix.diagonal (fun i : Fin s × Fin 3 => OneComponentScales.Multiplicity.nativeOneFrameScale E P v i.1 i.2)).mulVec u) i
  have hc := congrArg (fun t : Fin s × (Fin 3 × Fin 1) → ℂ =>
    (Quadratic.comparisonFrameMatrix B p).mulVec t (Multiplicity.OneIndex.Quadratic.singleFrameIndex s i)) hcoeff
  have hb := congrFun hphase (.inl (Multiplicity.OneIndex.Quadratic.singleFrameIndex s i))
  change ec (fr u) (.inr i) =
    Quadratic.comparisonFrameCoordinates B p (OneFrameComparison.Multiplicity.nativeOneFrameCoefficients E P hP hμ hs v hv u)
      (Multiplicity.OneIndex.Quadratic.singleFrameIndex s i) at hb
  exact hr.trans (hc.trans (hb.symm.trans (congrFun (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.lowerFrame_mulVec ec _ _ _ z.val u) i).symm))

theorem nativeOne_lowerFrame_det
    (hCoord : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification B (Intrinsic.OneTheta.Multiplicity.nativeOneFrames E P hP v))
    (hGeometry : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification B) (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    Quadratic.comparisonFrameDet B (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ z) *
      (∏ i : Fin s × Fin 3, OneComponentScales.Multiplicity.nativeOneFrameScale E P v i.1 i.2) =
        (Multiplicity.Period.nativeLowerFrame E P hP v (Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B) z.val).det := by
  exact Quadratic.comparisonFrameDeterminant B (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ z) (Multiplicity.OneIndex.Quadratic.singleFrameIndex s)
    (fun i : Fin s × Fin 3 => OneComponentScales.Multiplicity.nativeOneFrameScale E P v i.1 i.2) _
    (nativeOne_lowerFrame_matrix E P hP hμ hs v hv B hCoord hGeometry z)

end Multiplicity

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneFrameDeterminant
