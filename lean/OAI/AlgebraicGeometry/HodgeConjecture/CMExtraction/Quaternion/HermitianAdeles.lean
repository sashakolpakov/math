import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.FiniteUnitary
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.PointOne
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.LocalRational
import OAI.RepresentationTheory.Theta.Adelic.RationalSU

/-! # Hermitian Adeles -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.HermitianAdeles

noncomputable section

/-! The adelic quaternion map for a specified invertible Hermitian matrix
whose actual entries are the diagonal form, and its rational compatibility. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.IntegralTopology
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.RationalSU

variable (F : Type) [Field F] [NumberField F] {a : F}

def finiteFormCongr (H K : Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a)) (h : H = K) :
    RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup (fun v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F => RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H (.inr v)) →ₜ*
      RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup (fun v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F => RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F K (.inr v)) := by
  subst K
  exact ContinuousMonoidHom.id _

theorem finiteFormCongr_matrix (H K : Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a)) (h : H = K)
    (g : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup (fun v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F => RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H (.inr v)))
    (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) :
    (finiteFormCongr F H K h g v).val.val = (g v).val.val := by
  subst K
  rfl

theorem finiteFormCongr_includePlace (H K : Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a)) (h : H = K)
    (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H (.inr v))) :
    finiteFormCongr F H K h
      (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace (fun w : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F => RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H (.inr w)) v g) =
    RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace (fun w : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F => RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F K (.inr w)) v
      (CM.UnitaryPresentation.Quadratic.unitaryFormCongr _ _ (congrArg (fun M => RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F M (.inr v)) h) g) := by
  subst K
  rfl

variable (a b : F) (H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a))ˣ)
  (hH : H.val = UnitaryMatrixEquiv.Quadratic.diagonalForm (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) b))

theorem rationalFiniteSU_matrix (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H.val) (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) :
    (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU F H g v).val.val =
      g.val.val.map (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F a (.inr v)) := rfl

def quaternionFiniteHermitian :
    NumberTheory.Quaternion.Arithmetic.FiniteAdelicMatrices.FiniteAdelicGroupPoints (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) →ₜ* RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H :=
  (finiteFormCongr F _ _ hH.symm).comp (FiniteUnitary.quaternionFiniteUnitary F a b)

def quaternionRationalHermitian :
    (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)).RationalPoints →* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H.val :=
  (CM.UnitaryPresentation.Quadratic.unitaryFormCongr _ _ hH.symm).toMonoidHom.comp (PointOne.quaternionRationalUnitary a b)

def quaternionLocalHermitian (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) :
    NumberTheory.Quaternion.Arithmetic.LocalAdeles.LocalPoints (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) (.inr v) →ₜ*
      RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v)) where
  toMonoidHom := (CM.UnitaryPresentation.Quadratic.unitaryFormCongr _ _
    (congrArg (fun M => RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F M (.inr v)) hH.symm)).toMonoidHom.comp
      (LocalUnitary.quaternionLocalUnitary F a b v)
  continuous_toFun := (LocalUnitary.unitaryFormCongr_continuous _ _
    (congrArg (fun M => RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F M (.inr v)) hH.symm)).comp
      (LocalUnitary.quaternionLocalUnitary_continuous F a b v)

theorem quaternionFiniteHermitian_includePlace (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F)
    (g : NumberTheory.Quaternion.Arithmetic.LocalAdeles.LocalPoints (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) (.inr v)) :
    quaternionFiniteHermitian F a b H hH
      (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace (fun w => NumberTheory.Quaternion.Arithmetic.LocalAdeles.integralLocalSubgroup (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) (.inr w)) v g) =
    RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace (fun w : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F => RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H.val (.inr w)) v
      (quaternionLocalHermitian F a b H hH v g) := by
  change finiteFormCongr F _ _ hH.symm (FiniteUnitary.quaternionFiniteUnitary F a b _) = _
  rw [FiniteUnitary.quaternionFiniteUnitary_includePlace, finiteFormCongr_includePlace]
  rfl

omit [NumberField F] in
theorem quaternionRationalHermitian_matrix
    (g : (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)).RationalPoints) :
    (quaternionRationalHermitian F a b H hH g).val.val =
      (PointOne.quaternionRationalUnitary a b g).val.val := rfl

theorem quaternionFiniteHermitian_matrix
    (g : NumberTheory.Quaternion.Arithmetic.FiniteAdelicMatrices.FiniteAdelicGroupPoints (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)))
    (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) :
    (quaternionFiniteHermitian F a b H hH g v).val.val =
      (LocalUnitary.quaternionLocalUnitary F a b v (g v)).val.val :=
  finiteFormCongr_matrix F _ _ hH.symm (FiniteUnitary.quaternionFiniteUnitary F a b g) v

theorem quaternionFiniteHermitian_diagonal_matrix
    (g : (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)).RationalPoints)
    (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) :
    (quaternionFiniteHermitian F a b H hH
      (NumberTheory.Quaternion.Arithmetic.FiniteAdelicComparison.diagonalFiniteAdelic (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) g) v).val.val =
    (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU F H (quaternionRationalHermitian F a b H hH g) v).val.val := by
  exact (quaternionFiniteHermitian_matrix F a b H hH _ v).trans
    ((LocalRational.quaternionLocalUnitary_diagonal_matrix F a b v g).trans
      ((congrArg (fun M => M.map (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F a (.inr v)))
        (quaternionRationalHermitian_matrix F a b H hH g)).symm.trans
        (rationalFiniteSU_matrix (F := F) (H := H)
          (g := quaternionRationalHermitian F a b H hH g) (v := v)).symm))

theorem quaternionFiniteHermitian_diagonal
    (g : (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)).RationalPoints) :
    quaternionFiniteHermitian F a b H hH
      (NumberTheory.Quaternion.Arithmetic.FiniteAdelicComparison.diagonalFiniteAdelic (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) g) =
    RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU F H (quaternionRationalHermitian F a b H hH g) := by
  apply RestrictedProduct.ext
  intro v
  apply Subtype.ext
  apply Units.ext
  exact quaternionFiniteHermitian_diagonal_matrix F a b H hH g v

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.HermitianAdeles
