import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralAdelicCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientTopology

/-! # Adelic Tensor Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdelicTensorCoordinates.TestTransport

noncomputable section

section

/-! Compare number-field finite-adele positions with ReferenceFamily's original
rational finite-adele tensor coordinates, preserving rational vectors. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

open _root_.Module

variable (F : Type) [Field F] [NumberField F] (I : Type*) [Fintype I]

def coefficientPositionHomeomorph {J : Type*} [Fintype J] (b : Basis J ℚ F) :
    (I → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F) ≃ₜ ((I × J) → AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles) where
  toFun x ij := Finite.CoefficientTopology.TestTransport.finiteCoefficientBasisHomeomorph F b (x ij.1) ij.2
  invFun y i := (Finite.CoefficientTopology.TestTransport.finiteCoefficientBasisHomeomorph F b).symm (fun j => y (i, j))
  left_inv x := by
    funext i
    exact (Finite.CoefficientTopology.TestTransport.finiteCoefficientBasisHomeomorph F b).symm_apply_apply (x i)
  right_inv y := by
    funext ij
    exact congr_fun ((Finite.CoefficientTopology.TestTransport.finiteCoefficientBasisHomeomorph F b).apply_symm_apply
      (fun j => y (ij.1, j))) ij.2
  continuous_toFun := continuous_pi (fun ij => (continuous_apply ij.2).comp
    ((Finite.CoefficientTopology.TestTransport.finiteCoefficientBasisHomeomorph F b).continuous.comp (continuous_apply ij.1)))
  continuous_invFun := continuous_pi (fun i =>
    (Finite.CoefficientTopology.TestTransport.finiteCoefficientBasisHomeomorph F b).symm.continuous.comp
      (continuous_pi (fun j => continuous_apply (i, j))))

omit [Fintype I] in
theorem coefficientPositionHomeomorph_add {J : Type*} [Fintype J] (b : Basis J ℚ F)
    (x y : I → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F) :
    coefficientPositionHomeomorph F I b (x + y) =
      coefficientPositionHomeomorph F I b x + coefficientPositionHomeomorph F I b y := by
  funext ij
  exact congr_fun ((b.baseChange AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles).equivFun.map_add (x ij.1) (y ij.1)) ij.2

def adelicTensorHomeomorph : (I → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ≃ₜ (I → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F) :=
  (IntegralAdelicCoordinates.TestTransport.integralAdelicHomeomorph F I).trans (coefficientPositionHomeomorph F I (integralBasis F)).symm

theorem coefficientPositionHomeomorph_adelicTensor (x : I → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    coefficientPositionHomeomorph F I (integralBasis F) (adelicTensorHomeomorph F I x) =
      IntegralAdelicCoordinates.TestTransport.integralAdelicHomeomorph F I x :=
  (coefficientPositionHomeomorph F I (integralBasis F)).apply_symm_apply _

theorem adelicTensorHomeomorph_rational (x : I → F) :
    adelicTensorHomeomorph F I (IntegralAdelicCoordinates.TestTransport.fieldPositionDiagonal F I x) =
      fun i => AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding F (x i) := by
  apply (coefficientPositionHomeomorph F I (integralBasis F)).injective
  change coefficientPositionHomeomorph F I (integralBasis F)
    ((coefficientPositionHomeomorph F I (integralBasis F)).symm
      (IntegralAdelicCoordinates.TestTransport.integralAdelicHomeomorph F I (IntegralAdelicCoordinates.TestTransport.fieldPositionDiagonal F I x))) = _
  rw [Homeomorph.apply_symm_apply, IntegralAdelicCoordinates.TestTransport.integralAdelicHomeomorph_rational]
  funext ij
  exact (Finite.CoefficientTopology.TestTransport.finiteCoefficientBasisHomeomorph_rational F (integralBasis F) (x ij.1) ij.2).symm

theorem adelicTensorHomeomorph_add (x y : I → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    adelicTensorHomeomorph F I (x + y) =
      adelicTensorHomeomorph F I x + adelicTensorHomeomorph F I y := by
  apply (coefficientPositionHomeomorph F I (integralBasis F)).injective
  rw [coefficientPositionHomeomorph_add, coefficientPositionHomeomorph_adelicTensor,
    coefficientPositionHomeomorph_adelicTensor, coefficientPositionHomeomorph_adelicTensor,
    IntegralAdelicCoordinates.TestTransport.integralAdelicHomeomorph_add]

def adelicTensorAddEquiv : (I → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ≃+ (I → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F) where
  toEquiv := (adelicTensorHomeomorph F I).toEquiv
  map_add' := adelicTensorHomeomorph_add F I

def adelicTensorLinearEquiv : (I → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ≃L[ℚ] (I → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F) where
  toLinearEquiv :=
    { toAddEquiv := adelicTensorAddEquiv F I
      map_smul' := map_rat_smul (adelicTensorAddEquiv F I) }
  continuous_toFun := (adelicTensorHomeomorph F I).continuous
  continuous_invFun := (adelicTensorHomeomorph F I).symm.continuous

end

/-! The completion comparison is an actual ring isomorphism from the
number field's finite adeles to rational finite adeles tensor the field. -/

open scoped Classical _root_.NumberField

variable (F : Type) [Field F] [NumberField F]

def scalarAdelicTensorHomeomorph : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F ≃ₜ AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F :=
  ((Homeomorph.piUnique (fun _ : Unit => RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)).symm.trans
    (adelicTensorHomeomorph F Unit)).trans
      (Homeomorph.piUnique (fun _ : Unit => AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F))

theorem scalarAdelicTensorHomeomorph_rational (x : F) :
    scalarAdelicTensorHomeomorph F (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) x) =
      AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding F x :=
  congr_fun (adelicTensorHomeomorph_rational F Unit (fun _ => x)) ()

theorem scalarAdelicTensorHomeomorph_add (x y : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    scalarAdelicTensorHomeomorph F (x + y) =
      scalarAdelicTensorHomeomorph F x + scalarAdelicTensorHomeomorph F y :=
  congr_fun (adelicTensorHomeomorph_add F Unit (fun _ => x) (fun _ => y)) ()

theorem scalarAdelicTensorHomeomorph_mul (x y : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    scalarAdelicTensorHomeomorph F (x * y) =
      scalarAdelicTensorHomeomorph F x * scalarAdelicTensorHomeomorph F y := by
  let := Finite.CoefficientTopology.TestTransport.finiteCoefficients_t2 F
  have he : (fun p : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F × RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F =>
      scalarAdelicTensorHomeomorph F (p.1 * p.2)) =
      (fun p => scalarAdelicTensorHomeomorph F p.1 * scalarAdelicTensorHomeomorph F p.2) := by
    apply ((RepresentationTheory.Weil.AdelicSplitting.StrongApproximation.Construction.denseRange_rational_finiteAdeles F).prodMap
      (RepresentationTheory.Weil.AdelicSplitting.StrongApproximation.Construction.denseRange_rational_finiteAdeles F)).equalizer
      ((scalarAdelicTensorHomeomorph F).continuous.comp continuous_mul)
      ((Finite.CoefficientTopology.TestTransport.finiteCoefficient_mul_continuous F).comp
        ((scalarAdelicTensorHomeomorph F).continuous.prodMap
          (scalarAdelicTensorHomeomorph F).continuous))
    funext p
    change scalarAdelicTensorHomeomorph F
      (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) p.1 * algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) p.2) =
      scalarAdelicTensorHomeomorph F (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) p.1) *
        scalarAdelicTensorHomeomorph F (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) p.2)
    rw [← map_mul, scalarAdelicTensorHomeomorph_rational,
      scalarAdelicTensorHomeomorph_rational, scalarAdelicTensorHomeomorph_rational, map_mul]
  exact congr_fun he (x, y)

def scalarAdelicTensorRingEquiv : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F ≃+* AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F where
  toEquiv := (scalarAdelicTensorHomeomorph F).toEquiv
  map_add' := scalarAdelicTensorHomeomorph_add F
  map_mul' := scalarAdelicTensorHomeomorph_mul F

theorem scalarAdelicTensorRingEquiv_rational (x : F) :
    scalarAdelicTensorRingEquiv F (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) x) =
      AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding F x := scalarAdelicTensorHomeomorph_rational F x

theorem scalarAdelicTensorRingEquiv_continuous : Continuous (scalarAdelicTensorRingEquiv F) :=
  (scalarAdelicTensorHomeomorph F).continuous

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdelicTensorCoordinates.TestTransport
