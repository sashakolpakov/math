import OAI.NumberTheory.Quaternion.Arithmetic.MatrixGroup
import OAI.NumberTheory.Quaternion.Arithmetic.LocalGeneration

/-! # Matrix Scalar Map -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.MatrixScalarMap

noncomputable section

section

/-! The polynomial matrix realization and the complete normed local
quaternion model have the same local group topology. -/

open scoped Classical _root_.Quaternion
open QuaternionAlgebra _root_.Matrix _root_.Topology

variable (F K : Type) [Field F] [NontriviallyNormedField K] [Algebra F K] (a b : F)

def localQuaternionMatrixPointsEquiv :
    (LocalModel.localQuaternionUnitNorm F K a b).ker ≃* (MatrixGroup.quaternionNormOneMatrixGroup a b).Points (algebraMap F K) :=
  (LocalGeneration.localQuaternionNormOneEquiv F K a b).symm.trans (MatrixGroup.quaternionMatrixPointsEquiv a b (algebraMap F K))

theorem localQuaternionMatrixPointsEquiv_matrix (q : (LocalModel.localQuaternionUnitNorm F K a b).ker) :
    PolynomialGaloisNorm.matrixPointsHom (MatrixGroup.quaternionNormOneMatrixGroup a b) (algebraMap F K)
      (localQuaternionMatrixPointsEquiv F K a b q) =
    MatrixQuaternionDet.quaternionRegularMatrix (algebraMap F K a) (algebraMap F K b)
      ((LocalModel.localQuaternionModelEquiv F K a b).symm q.val.val) := rfl

def quaternionFirstColumnLinear (a b : K) : Matrix (Fin 4) (Fin 4) K →ₗ[K] ℍ[K,a,b] where
  toFun := MatrixQuaternionDet.quaternionFirstColumn a b
  map_add' M N := by apply QuaternionAlgebra.ext <;> rfl
  map_smul' c M := by apply QuaternionAlgebra.ext <;> rfl

theorem localQuaternionMatrixPointsEquiv_symm_val
    (g : (MatrixGroup.quaternionNormOneMatrixGroup a b).Points (algebraMap F K)) :
    ((localQuaternionMatrixPointsEquiv F K a b).symm g).val.val =
      LocalModel.localQuaternionModelEquiv F K a b
        (MatrixQuaternionDet.quaternionFirstColumn (algebraMap F K a) (algebraMap F K b)
          (PolynomialGaloisNorm.matrixPointsHom (MatrixGroup.quaternionNormOneMatrixGroup a b) (algebraMap F K) g)) := by
  let e := localQuaternionMatrixPointsEquiv F K a b
  have he := localQuaternionMatrixPointsEquiv_matrix F K a b (e.symm g)
  change PolynomialGaloisNorm.matrixPointsHom (MatrixGroup.quaternionNormOneMatrixGroup a b) (algebraMap F K) (e (e.symm g)) = _ at he
  rw [MulEquiv.apply_symm_apply] at he
  have hc := congrArg (MatrixQuaternionDet.quaternionFirstColumn (algebraMap F K a) (algebraMap F K b)) he
  have hfirst : MatrixQuaternionDet.quaternionFirstColumn (algebraMap F K a) (algebraMap F K b)
      (MatrixQuaternionDet.quaternionRegularMatrix (algebraMap F K a) (algebraMap F K b)
        ((LocalModel.localQuaternionModelEquiv F K a b).symm (e.symm g).val.val)) =
      (LocalModel.localQuaternionModelEquiv F K a b).symm (e.symm g).val.val :=
    MatrixQuaternionDet.quaternionRegularMatrix_firstColumn _ _ _
  rw [hfirst] at hc
  have hmap := congrArg (LocalModel.localQuaternionModelEquiv F K a b) hc
  exact (hmap.trans ((LocalModel.localQuaternionModelEquiv F K a b).apply_symm_apply _)).symm

theorem localQuaternionMatrixPointsEquiv_continuous [CompleteSpace K] :
    Continuous (localQuaternionMatrixPointsEquiv F K a b) := by
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  change Continuous (fun q : (LocalModel.localQuaternionUnitNorm F K a b).ker =>
    PolynomialGaloisNorm.matrixPointsHom (MatrixGroup.quaternionNormOneMatrixGroup a b) (algebraMap F K)
      (localQuaternionMatrixPointsEquiv F K a b q))
  simp only [localQuaternionMatrixPointsEquiv_matrix]
  let L := (MatrixQuaternionDet.quaternionRegularMatrix (algebraMap F K a) (algebraMap F K b)).toLinearMap.comp
    (LocalModel.localQuaternionModelEquiv F K a b).symm.toLinearMap
  have hL : Continuous L := L.continuous_of_finiteDimensional
  exact hL.comp (Units.continuous_val.comp continuous_subtype_val)

theorem localQuaternionMatrixPointsEquiv_symm_continuous [CompleteSpace K] :
    Continuous (localQuaternionMatrixPointsEquiv F K a b).symm := by
  apply continuous_induced_rng.mpr
  apply (IsOpenUnits.isOpenEmbedding_unitsVal (M := LocalModel.localQuaternionModel F K a b)).isEmbedding.continuous_iff.mpr
  change Continuous (fun g => ((localQuaternionMatrixPointsEquiv F K a b).symm g).val.val)
  simp only [localQuaternionMatrixPointsEquiv_symm_val]
  let L := (LocalModel.localQuaternionModelEquiv F K a b).toLinearMap.comp
    (quaternionFirstColumnLinear K (algebraMap F K a) (algebraMap F K b))
  have hL : Continuous L := L.continuous_of_finiteDimensional
  exact hL.comp (continuous_subtype_val.comp continuous_subtype_val)

def localQuaternionMatrixPointsHomeomorph [CompleteSpace K] :
    (LocalModel.localQuaternionUnitNorm F K a b).ker ≃ₜ*
      (MatrixGroup.quaternionNormOneMatrixGroup a b).Points (algebraMap F K) where
  toMulEquiv := localQuaternionMatrixPointsEquiv F K a b
  continuous_toFun := localQuaternionMatrixPointsEquiv_continuous F K a b
  continuous_invFun := localQuaternionMatrixPointsEquiv_symm_continuous F K a b

end

/-! Scalar extension commutes with the faithful quaternion matrix
realization and its maps on norm-one points. -/

open scoped Classical _root_.Quaternion _root_.Matrix
open QuaternionAlgebra _root_.Matrix

variable {F K : Type} [Field F] [Field K]

theorem quaternionRegularMatrix_map (ρ : F →+* K) (a b : F) (q : ℍ[F,a,b]) :
    (MatrixQuaternionDet.quaternionRegularMatrix a b q).map ρ =
      MatrixQuaternionDet.quaternionRegularMatrix (ρ a) (ρ b) (ConjugationQuaternion.quaternionCoefficientMap ρ a b q) := by
  rw [MatrixQuaternionDet.quaternionRegularMatrix_apply, MatrixQuaternionDet.quaternionRegularMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, ConjugationQuaternion.quaternionCoefficientMap, Matrix.cons_val_two, Matrix.cons_val_three]

def quaternionNormOneCoefficientMap (ρ : F →+* K) (a b : F) :
    (Norm.quaternionUnitNorm a b).ker →* (Norm.quaternionUnitNorm (ρ a) (ρ b)).ker :=
  ((Units.map (ConjugationQuaternion.quaternionCoefficientMap ρ a b).toMonoidHom).comp
    (Norm.quaternionUnitNorm a b).ker.subtype).codRestrict (Norm.quaternionUnitNorm (ρ a) (ρ b)).ker (by
      intro q
      apply MonoidHom.mem_ker.mpr
      apply Units.ext
      change Norm.quaternionNorm (ρ a) (ρ b) (ConjugationQuaternion.quaternionCoefficientMap ρ a b q.val.val) = 1
      rw [ConjugationQuaternion.quaternionCoefficientMap_norm]
      have hn : Norm.quaternionNorm a b q.val.val = 1 := congrArg Units.val (MonoidHom.mem_ker.mp q.property)
      rw [hn, map_one])

theorem quaternionMatrixPointsEquiv_coefficientMap (ρ : F →+* K) (a b : F)
    (q : (Norm.quaternionUnitNorm a b).ker) :
    (MatrixGroup.quaternionNormOneMatrixGroup a b).map (RingHom.id F) ρ
      (MatrixGroup.quaternionMatrixPointsEquiv a b (RingHom.id F) q) =
    MatrixGroup.quaternionMatrixPointsEquiv a b ρ (quaternionNormOneCoefficientMap ρ a b q) := by
  apply PolynomialGaloisNorm.matrixPointsHom_injective (MatrixGroup.quaternionNormOneMatrixGroup a b) ρ
  change (MatrixQuaternionDet.quaternionRegularMatrix a b q.val.val).map ρ =
    MatrixQuaternionDet.quaternionRegularMatrix (ρ a) (ρ b) (ConjugationQuaternion.quaternionCoefficientMap ρ a b q.val.val)
  exact quaternionRegularMatrix_map ρ a b q.val.val

end

end OAI.NumberTheory.Quaternion.Arithmetic.MatrixScalarMap
