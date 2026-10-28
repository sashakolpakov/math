import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OneCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneTensorComplex
import OAI.RepresentationTheory.Hecke.RadialDilation.RationalCoordinates

/-! # One Complex Components -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneComplexComponents

noncomputable section

section

/-! Linear normalization of the original paired CM embedding components.
On every rational vector it is exactly AdelicTheta's real tensor realization. -/

open scoped Classical _root_.NumberField Kronecker
open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta

namespace Quadratic

variable {F : Type} [Field F] [NumberField F] {d : F}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {K : (Matrix (Fin 1) (Fin 1) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}

def oneComponentNormalizer (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d 1 H K) (v : Fin A.places) :
    Matrix (Fin 3 × Fin 1) (Fin 3 × Fin 1) ℂ :=
  (A.basisV v).inv ⊗ₖ (A.basisP v).inv

def oneComplexComponents (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d 1 H K) :
    (Fin A.places → ((Fin 3 → ℂ) × (Fin 3 → ℂ))) →ₗ[ℂ] RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase A where
  toFun w v :=
    ((oneComponentNormalizer A v).mulVec (fun ij => (w v).1 ij.1),
      fun ij => (if v = A.distinguished ∧ ij.1 = 2 then (-1 : ℂ) else 1) *
        (if A.positive v ij.2 then (1 : ℂ) else -1) *
        ((oneComponentNormalizer A v).map star).mulVec (fun ij => (w v).2 ij.1) ij)
  map_add' x y := by
    funext v
    apply Prod.ext <;> funext ij <;>
      simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  map_smul' c w := by
    funext v
    apply Prod.ext <;> funext ij <;>
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

theorem realTensorComponents_one_eq (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d 1 H K)
    (t : ∀ i : Fin A.places,
      RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate i)) d) 3 1)
    (w : Fin A.places → Fin 3 → ℂ)
    (h : ∀ i j, A.complex i (t i j) = w i j.1) :
    RepresentationTheory.Theta.Adelic.BallGeometryData.realTensorComponents A t =
      oneComplexComponents A (fun i => (w i, fun j => star (w i j))) := by
  funext i
  dsimp only [RepresentationTheory.Theta.Adelic.BallGeometryData.realTensorComponents, oneComplexComponents, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [h]
  apply Prod.ext
  · rfl
  · funext ij
    exact congrArg (fun z : ℂ =>
      (if i = A.distinguished ∧ ij.1 = 2 then (-1 : ℂ) else 1) *
        (if A.positive i ij.2 then (1 : ℂ) else -1) * z)
      (congrFun (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.conjugate_mulVec (oneComponentNormalizer A i)
        (fun j => w i j.1)) ij)

end Quadratic

namespace Multiplicity

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (hs : 2 ≤ s) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)

theorem nativeOne_rational_components (x : Fin 3 → E) :
    RepresentationTheory.Theta.Adelic.BallGeometryData.realTensorComponents (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv)
      (fun i j => RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneParameter E P hP)
        (.inl ((Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv).enumerate i))
        (Multiplicity.OneTrace.Quadratic.singleTensorPosition E P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
          (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP) x j)) =
      Quadratic.oneComplexComponents (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv)
        (fun i => (fun j => P.embeddings i (x j), fun j => star (P.embeddings i (x j)))) := by
  apply Quadratic.realTensorComponents_one_eq
  intro i j
  exact (Intrinsic.OneCoordinates.Multiplicity.nativeOneBall_embedding E P hP hμ hs v hv i
    (Multiplicity.OneTrace.Quadratic.singleTensorPosition E P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
      (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP) x j)).trans
    (congrArg (P.embeddings i)
      ((ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
        (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP)).apply_symm_apply _))

end Multiplicity

end

/-! The complexification of the constructed native rational coordinates
agrees with the actual paired CM component normalization. -/

open scoped Classical _root_.NumberField TensorProduct
open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization

namespace Quadratic

def singleComplexPhaseReindex (n : ℕ) :
    (((Fin n × (Fin 3 × Fin 1)) ⊕ (Fin n × (Fin 3 × Fin 1))) → ℂ) ≃ₗ[ℂ]
      (((Fin n × Fin 3) ⊕ (Fin n × Fin 3)) → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (Equiv.sumCongr (Multiplicity.OneIndex.Quadratic.singleFrameIndex n) (Multiplicity.OneIndex.Quadratic.singleFrameIndex n))

end Quadratic

namespace Multiplicity

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (hs : 2 ≤ s) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP)
    (Intrinsic.OneTheta.Multiplicity.nativeOneSkew E P hP v) (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv))

def nativeOneComplexCoordinates : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) ≃ₗ[ℂ]
    RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv) :=
  (((RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates E P.embeddings hP.1
    (Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B)).trans
      (Quadratic.singleComplexPhaseReindex s).symm).trans
        (Multiplicity.OneCoordinates.Quadratic.phaseSwapEquiv (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv)) ℂ)).trans
          B.complexPhase.toLinearEquiv

theorem nativeOneComplexCoordinates_rational
    (hCoord : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification B (Intrinsic.OneTheta.Multiplicity.nativeOneFrames E P hP v))
    (x : Fin 3 → E) :
    nativeOneComplexCoordinates E P hP hμ hs v hv B (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings x) =
      Quadratic.oneComplexComponents (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv) (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings x) := by
  have hr := RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates_tmul E P.embeddings hP.1
    (Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B) (1 : ℂ) x
  rw [RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.pairedComplexification_tmul E P.embeddings hP.1 (1 : ℂ) x,
    one_smul, one_smul] at hr
  change B.complexPhase (RepresentationTheory.Theta.Adelic.DataTheta.swapPhase ((Quadratic.singleComplexPhaseReindex s).symm
    (RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates E P.embeddings hP.1
      (Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B) (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings x)))) = _
  rw [hr]
  have he :
      RepresentationTheory.Theta.Adelic.DataTheta.swapPhase ((Quadratic.singleComplexPhaseReindex s).symm
        (fun i => (Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B x i : ℂ))) =
      (fun i => (B.rationalPhase ((Intrinsic.OneTheta.Multiplicity.nativeOneFrames E P hP v).rational.coordinates
        (Multiplicity.OneTrace.Quadratic.singleTensorPosition E P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
          (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP) x)) i : ℂ)) := by
    funext i
    cases i with
    | inl j =>
      rcases j with ⟨i, j, k⟩
      have hk : k = 0 := Subsingleton.elim _ _
      subst k
      rfl
    | inr j =>
      rcases j with ⟨i, j, k⟩
      have hk : k = 0 := Subsingleton.elim _ _
      subst k
      rfl
  exact (congrArg B.complexPhase he).trans ((OneTensorComplex.Quadratic.complexPhase_rational_tensor B (Intrinsic.OneTheta.Multiplicity.nativeOneFrames E P hP v) hCoord
    (Multiplicity.OneTrace.Quadratic.singleTensorPosition E P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
      (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP) x)).trans
        (nativeOne_rational_components E P hP hμ hs v hv x))

theorem nativeOneComplexCoordinates_components
    (hCoord : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification B (Intrinsic.OneTheta.Multiplicity.nativeOneFrames E P hP v))
    (w : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) :
    nativeOneComplexCoordinates E P hP hμ hs v hv B w =
      Quadratic.oneComplexComponents (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv) w := by
  obtain ⟨t, rfl⟩ := (RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.pairedComplexification E P.embeddings hP.1).surjective w
  let f := (nativeOneComplexCoordinates E P hP hμ hs v hv B).toLinearMap.comp
    (RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.pairedComplexification E P.embeddings hP.1).toLinearMap
  let g : (ℂ ⊗[ℚ] (Fin 3 → E)) →ₗ[ℂ]
      RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv) :=
    (Quadratic.oneComplexComponents (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv)).comp
      (RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.pairedComplexification E P.embeddings hP.1).toLinearMap
  change f t = g t
  induction t using TensorProduct.inductionOn with
  | add t u ht hu => simp only [map_add, ht, hu]
  | tmul c x =>
      change nativeOneComplexCoordinates E P hP hμ hs v hv B
        (RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.pairedComplexification E P.embeddings hP.1 (c ⊗ₜ[ℚ] x)) =
          Quadratic.oneComplexComponents (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv)
            (RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.pairedComplexification E P.embeddings hP.1 (c ⊗ₜ[ℚ] x))
      rw [RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.pairedComplexification_tmul E P.embeddings hP.1 c x]
      exact ((nativeOneComplexCoordinates E P hP hμ hs v hv B).map_smul c _).trans
        ((congrArg (fun y => c • y)
          (nativeOneComplexCoordinates_rational E P hP hμ hs v hv B hCoord x)).trans
            ((Quadratic.oneComplexComponents (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv)).map_smul c _).symm)

end Multiplicity

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneComplexComponents
