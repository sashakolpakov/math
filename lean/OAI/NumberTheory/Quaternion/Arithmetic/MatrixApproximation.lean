import OAI.NumberTheory.Quaternion.Arithmetic.MatrixScalarMap
import OAI.NumberTheory.Quaternion.Arithmetic.LocalModel
import OAI.NumberTheory.Quaternion.Arithmetic.Product
import OAI.NumberTheory.Quaternion.Arithmetic.ExceptionalApproximation

/-! # Matrix Approximation -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.MatrixApproximation

noncomputable section

/-! Weak approximation and almost-all-place additive generation for
the actual polynomial quaternion matrix group used in Arithmetic. -/

open scoped Classical _root_.Quaternion _root_.NumberField
open IsDedekindDomain Filter

variable {F : Type} [Field F] [NumberField F] {ι : Type*} [Fintype ι]
  (v : ι → HeightOneSpectrum (𝓞 F)) (a b : F)

omit [Fintype ι] in
theorem quaternionMatrix_diagonal_compat (q : (Norm.quaternionUnitNorm a b).ker) (i : ι) :
    MatrixScalarMap.localQuaternionMatrixPointsHomeomorph F ((v i).adicCompletion F) a b
      (LocalModel.quaternionNormOneDiagonal v a b q i) =
    LocalAdeles.diagonalLocal (MatrixGroup.quaternionNormOneMatrixGroup a b) (.inr (v i))
      (MatrixGroup.quaternionMatrixPointsEquiv a b (RingHom.id F) q) := by
  let ρ := algebraMap F ((v i).adicCompletion F)
  apply PolynomialGaloisNorm.matrixPointsHom_injective (MatrixGroup.quaternionNormOneMatrixGroup a b) ρ
  change MatrixQuaternionDet.quaternionRegularMatrix (ρ a) (ρ b)
      ((LocalModel.localQuaternionModelEquiv F ((v i).adicCompletion F) a b).symm
        (LocalModel.localQuaternionModelEquiv F ((v i).adicCompletion F) a b
          (ConjugationQuaternion.quaternionCoefficientMap ρ a b q.val.val))) = (MatrixQuaternionDet.quaternionRegularMatrix a b q.val.val).map ρ
  rw [AlgEquiv.symm_apply_apply]
  exact (MatrixScalarMap.quaternionRegularMatrix_map ρ a b q.val.val).symm

theorem denseRange_quaternionMatrix_finite_projection (hv : Function.Injective v)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    DenseRange (Product.diagonalFiniteProduct (MatrixGroup.quaternionNormOneMatrixGroup a b) v) := by
  let G := MatrixGroup.quaternionNormOneMatrixGroup a b
  let E : (∀ i, (LocalModel.localQuaternionUnitNorm F ((v i).adicCompletion F) a b).ker) →
      (∀ i, LocalAdeles.LocalPoints G (.inr (v i))) :=
    fun x i => MatrixScalarMap.localQuaternionMatrixPointsHomeomorph F ((v i).adicCompletion F) a b (x i)
  have hE : Continuous E := continuous_pi fun i =>
    (MatrixScalarMap.localQuaternionMatrixPointsHomeomorph F ((v i).adicCompletion F) a b).continuous.comp (continuous_apply i)
  have hs : Function.Surjective E := by
    intro x
    refine ⟨fun i => (MatrixScalarMap.localQuaternionMatrixPointsHomeomorph F ((v i).adicCompletion F) a b).symm (x i), ?_⟩
    funext i
    exact (MatrixScalarMap.localQuaternionMatrixPointsHomeomorph F ((v i).adicCompletion F) a b).apply_symm_apply (x i)
  have hd := hs.denseRange.comp (LocalModel.denseRange_quaternionNormOneDiagonal v a b hv ha hb) hE
  apply hd.mono
  rintro x ⟨q, rfl⟩
  refine ⟨MatrixGroup.quaternionMatrixPointsEquiv a b (RingHom.id F) q, ?_⟩
  funext i
  exact (quaternionMatrix_diagonal_compat v a b q i).symm

theorem eventually_quaternionMatrix_local_additive_generation (ha : a ≠ 0) (hb : b ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 F) in cofinite,
      ExceptionalApproximation.localAdditiveGeneration (MatrixGroup.quaternionNormOneMatrixGroup a b) (.inr w) := by
  filter_upwards [LocalGeneration.eventually_localQuaternion_additive_generation a b ha hb] with w hw
  exact AdditiveGenerationTransport.additive_generation_of_mulEquiv (K := w.adicCompletion F)
    (MatrixScalarMap.localQuaternionMatrixPointsEquiv F (w.adicCompletion F) a b) hw

end

end OAI.NumberTheory.Quaternion.Arithmetic.MatrixApproximation
