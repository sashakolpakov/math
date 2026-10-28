import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TransportedGeometricFirst
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneHalfFrame
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CotangentTheta

/-! # Transported Form -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.TransportedForm.Multiplicity

/-! The retained native finite test is transported to the actual AdelicTheta
restricted tensor space. Its distinguished first coefficients are
identified in the original native frame. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneHalfFrame.Quadratic

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (hs : 2 ≤ s) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData (maximalRealSubfield E) (OneTheta.Multiplicity.nativeOneHermitian E P hP)
    (OneTheta.Multiplicity.nativeOneSkew E P hP v) (OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv))

def nativeOneFiniteTest (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3)) :
    RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz (maximalRealSubfield E) (3 * 1) :=
  Finite.BasisTransport.Test.transportBasisTest (OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv) B.rationalPosition
    (Finite.BasisTransport.Test.reindexFiniteTest (Multiplicity.OneIndex.Quadratic.singleFrameIndex s) φ)

theorem nativeOneFiniteTest_rational_value (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3))
    (x : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position (maximalRealSubfield E) (3 * 1)) :
    RepresentationTheory.Theta.Adelic.DataTheta.rationalWeight (nativeOneFiniteTest E P hP hμ hs v hv B φ) x =
      φ.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (fun i => B.rationalPosition x (Multiplicity.OneIndex.Quadratic.singleFrameIndex s i))) := by
  unfold RepresentationTheory.Theta.Adelic.DataTheta.rationalWeight nativeOneFiniteTest
  rw [show (fun i => algebraMap (maximalRealSubfield E)
    (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles (maximalRealSubfield E)) (x i)) =
      RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x from rfl,
    Finite.BasisTransport.Test.transportBasisTest_rational_value]
  rfl

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

theorem nativeOneFiniteTest_geometric_slot
    (hCoord : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification B (OneTheta.Multiplicity.nativeOneFrames E P hP v))
    (hGeometry : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification B)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3)) (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain})
    (i : Fin 2) :
    RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.geometricFirst B (nativeOneFiniteTest E P hP hμ hs v hv B φ)
        (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ z)
        (TransportedGeometricFirst.TestTransport.comparisonSlotVector (A := OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv) i) =
      (B.halfFrame (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ z))⁻¹ *
        (-(OneDiagonalNormalizer.Multiplicity.nativeOneScale E P v P.distinguished : ℂ) *
          FamilyTheta.Multiplicity.nativeFrameTheta E P hP hμ v hv
            (OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B)
            (OneCoordinates.Multiplicity.nativeOneRationalCoordinates_pairing E P hP hμ hs v hv B hCoord) φ z i) := by
  let e := OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B
  let he := OneCoordinates.Multiplicity.nativeOneRationalCoordinates_pairing E P hP hμ hs v hv B hCoord
  have hZ := (OneFrameDeterminant.Multiplicity.nativeOne_period_matrix E P hP hμ hs v hv B hCoord hGeometry z).symm
  have hL := OneFrameDeterminant.Multiplicity.nativeOne_lowerFrame_matrix E P hP hμ hs v hv B hCoord hGeometry z
  have hd := PeriodFamily.Multiplicity.native_lowerFrame_det E P hP hμ v hv e he z.val z.property
  have ht := TransportedGeometricFirst.TestTransport.transported_geometricFirst_basis B (Multiplicity.OneIndex.Quadratic.singleFrameIndex s) φ
    (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ z) (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he z) hZ
    (fun j : Fin s × Fin 3 => OneComponentScales.Multiplicity.nativeOneFrameScale E P v j.1 j.2)
    (Multiplicity.Period.nativeLowerFrame E P hP v e z.val) hL hd (P.distinguished, i.succ)
  have hc : OneComponentScales.Multiplicity.nativeOneFrameScale E P v P.distinguished i.succ =
      -(OneDiagonalNormalizer.Multiplicity.nativeOneScale E P v P.distinguished : ℂ) := by
    fin_cases i <;> simp [OneComponentScales.Multiplicity.nativeOneFrameScale]
  rw [hc] at ht
  exact ht

end AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.TransportedForm.Multiplicity

namespace AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.TransportedForm

/-! The actual AdelicTheta one-form of the transported test equals the original
native cotangent theta form times one fixed nonzero scalar. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection

namespace TestTransport

def cotangentBasisVector (i : Fin 2) : Fin 2 → ℂ := Pi.single i 1

theorem cotangent_ext_on_basis (f g : (Fin 2 → ℂ) →L[ℂ] ℂ)
    (h : ∀ i, f (cotangentBasisVector i) = g (cotangentBasisVector i)) : f = g := by
  apply ContinuousLinearMap.ext
  intro u
  rw [RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.cotangent_expansion, RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.cotangent_expansion]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun a : ℂ => u i * a) (h i)

theorem slotEmbedding_single
    {F : Type} [Field F] [NumberField F] {d : F}
    {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
    {K : (Matrix (Fin 1) (Fin 1) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
    {A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d 1 H K} (i : Fin 2) :
    RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.slotEmbedding (A := A) (Pi.single i 1) = Pi.single (RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.slot (A := A) i) 1 := by
  fin_cases i <;> simp [RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.slotEmbedding]

theorem comparisonThetaOneForm_single
    {F : Type} [Field F] [NumberField F] {d : F}
    {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
    {K : (Matrix (Fin 1) (Fin 1) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
    {A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d 1 H K} (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H K A)
    (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * 1)) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (i : Fin 2) :
    RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B f z (cotangentBasisVector i) = RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.geometricFirst B f z (TransportedGeometricFirst.TestTransport.comparisonSlotVector i) := by
  change RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B f z (Pi.single i 1) = _
  rw [RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm_apply, slotEmbedding_single]
  rfl

end TestTransport

namespace Multiplicity
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneHalfFrame.Quadratic

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (hs : 2 ≤ s) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData (maximalRealSubfield E) (OneTheta.Multiplicity.nativeOneHermitian E P hP)
    (OneTheta.Multiplicity.nativeOneSkew E P hP v) (OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv))

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

def nativeOneThetaFactor (hCoord : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification B (OneTheta.Multiplicity.nativeOneFrames E P hP v)) : ℂ :=
  -(OneDiagonalNormalizer.Multiplicity.nativeOneScale E P v P.distinguished : ℂ) *
    (B.halfFrame (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ (PeriodDomain.Multiplicity.nativeOrigin E P hP)) /
      FrameRoot.Multiplicity.nativeFrameRoot E P hP hμ v hv (OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B)
        (OneCoordinates.Multiplicity.nativeOneRationalCoordinates_pairing E P hP hμ hs v hv B hCoord)
        (PeriodDomain.Multiplicity.nativeOrigin E P hP))⁻¹

theorem nativeOneThetaFactor_ne_zero
    (hCoord : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification B (OneTheta.Multiplicity.nativeOneFrames E P hP v))
    (hGeometry : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification B) :
    nativeOneThetaFactor E P hP hμ hs v hv B hCoord ≠ 0 := by
  apply mul_ne_zero
  · exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr
      (OneDiagonalNormalizer.Multiplicity.nativeOneScale_pos E P hP hμ v P.distinguished).ne')
  · exact inv_ne_zero (div_ne_zero (hGeometry.2.2.2.2.2.1 _).1
      (FrameRoot.Multiplicity.nativeFrameRoot_ne_zero E P hP hμ v hv _ _ _))

theorem nativeOneFiniteTest_thetaOneForm
    (hCoord : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification B (OneTheta.Multiplicity.nativeOneFrames E P hP v))
    (hGeometry : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification B)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3)) (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B (nativeOneFiniteTest E P hP hμ hs v hv B φ)
        (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ z) =
      nativeOneThetaFactor E P hP hμ hs v hv B hCoord •
        CotangentTheta.Multiplicity.nativeCotangentThetaOneForm E P hP hμ v hv
          (OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B)
          (OneCoordinates.Multiplicity.nativeOneRationalCoordinates_pairing E P hP hμ hs v hv B hCoord) φ z.val := by
  let e := OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B
  let he := OneCoordinates.Multiplicity.nativeOneRationalCoordinates_pairing E P hP hμ hs v hv B hCoord
  apply TestTransport.cotangent_ext_on_basis
  intro i
  refine (TestTransport.comparisonThetaOneForm_single B
    (nativeOneFiniteTest E P hP hμ hs v hv B φ) (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ z) i).trans
    ((nativeOneFiniteTest_geometric_slot E P hP hμ hs v hv B hCoord hGeometry φ z i).trans ?_)
  have hvalue : FrameProjection.Multiplicity.coordinateCovector (FamilyTheta.Multiplicity.nativeFrameTheta E P hP hμ v hv e he φ z)
      (TestTransport.cotangentBasisVector i) = FamilyTheta.Multiplicity.nativeFrameTheta E P hP hμ v hv e he φ z i := by
    rw [FrameProjection.Multiplicity.coordinateCovector_apply]
    simp [TestTransport.cotangentBasisVector, Pi.single_apply]
  rw [CotangentTheta.Multiplicity.nativeCotangentThetaOneForm_coordinates E P hP hμ v hv e he φ z,
    smul_apply, smul_apply, hvalue]
  rw [OneHalfFrame.Multiplicity.nativeOne_halfFrame_constant E P hP hμ hs v hv B hCoord hGeometry z]
  simp only [nativeOneThetaFactor, mul_inv_rev, smul_eq_mul]
  ring

end Multiplicity

end AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.TransportedForm

end

end OAI
