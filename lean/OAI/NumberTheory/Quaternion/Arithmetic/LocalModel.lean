import OAI.NumberTheory.Quaternion.Arithmetic.ConjugationQuaternion

/-! # Local Model -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.LocalModel

noncomputable section

section

/-! Complete normed local quaternion models, with their coefficient
maps, reduced norms, and proved norm-one commutator generation. -/

open scoped Classical _root_.Quaternion
open QuaternionAlgebra

variable (F K : Type*) [Field F] [NontriviallyNormedField K] [Algebra F K] (a b : F)

abbrev localQuaternionModel :=
  NoncommutativeLocalModel.finiteAlgebraNormedModel K ℍ[K,algebraMap F K a,algebraMap F K b]

def localQuaternionModelEquiv :
    ℍ[K,algebraMap F K a,algebraMap F K b] ≃ₐ[K] localQuaternionModel F K a b :=
  NoncommutativeLocalModel.finiteAlgebraNormedModelEquiv K _

instance localQuaternionBaseAlgebra : Algebra F (localQuaternionModel F K a b) :=
  Algebra.compHom (localQuaternionModel F K a b) (algebraMap F K)

instance localQuaternionTower : IsScalarTower F K (localQuaternionModel F K a b) :=
  IsScalarTower.of_algebraMap_eq' rfl

def localQuaternionCoefficients : ℍ[F,a,b] →ₐ[F] localQuaternionModel F K a b :=
  ((localQuaternionModelEquiv F K a b).toAlgHom.restrictScalars F).comp (ConjugationQuaternion.quaternionCoefficientAlgHom a b)

theorem localQuaternionCoefficients_injective : Function.Injective (localQuaternionCoefficients F K a b) :=
  (localQuaternionModelEquiv F K a b).injective.comp (ConjugationQuaternion.quaternionCoefficientMap_injective _ a b)

def localQuaternionBasis : Module.Basis (Fin 4) K (localQuaternionModel F K a b) :=
  (basisOneIJK (algebraMap F K a) 0 (algebraMap F K b)).map
    (localQuaternionModelEquiv F K a b).toLinearEquiv

theorem localQuaternionBasis_apply (j : Fin 4) :
    localQuaternionBasis F K a b j = localQuaternionCoefficients F K a b (basisOneIJK a 0 b j) := by
  change localQuaternionModelEquiv F K a b (basisOneIJK (algebraMap F K a) 0 (algebraMap F K b) j) = _
  rw [← ConjugationQuaternion.quaternionCoefficientMap_basis (algebraMap F K) a b j]
  rfl

def localQuaternionUnitMap : ℍ[F,a,b]ˣ →* (localQuaternionModel F K a b)ˣ :=
  Units.map (localQuaternionCoefficients F K a b).toMonoidHom

def localQuaternionUnitNorm : (localQuaternionModel F K a b)ˣ →* Kˣ :=
  (Norm.quaternionUnitNorm (algebraMap F K a) (algebraMap F K b)).comp
    (Units.map (localQuaternionModelEquiv F K a b).symm.toMonoidHom)

theorem localQuaternionUnitNorm_map (q : ℍ[F,a,b]ˣ) :
    localQuaternionUnitNorm F K a b (localQuaternionUnitMap F K a b q) =
      Units.map (algebraMap F K).toMonoidHom (Norm.quaternionUnitNorm a b q) := by
  apply Units.ext
  change Norm.quaternionNorm (algebraMap F K a) (algebraMap F K b)
    ((localQuaternionModelEquiv F K a b).symm
      (localQuaternionModelEquiv F K a b (ConjugationQuaternion.quaternionCoefficientMap (algebraMap F K) a b q.val))) = _
  rw [AlgEquiv.symm_apply_apply]
  exact ConjugationQuaternion.quaternionCoefficientMap_norm _ a b q.val

theorem localQuaternionUnitNorm_ker_le_commutator [CharZero K] (ha : a ≠ 0) (hb : b ≠ 0) :
    (localQuaternionUnitNorm F K a b).ker ≤ commutator (localQuaternionModel F K a b)ˣ := by
  intro q hq
  let e := Units.mapEquiv (localQuaternionModelEquiv F K a b).toMulEquiv
  have hn : e.symm q ∈ (Norm.quaternionUnitNorm (algebraMap F K a) (algebraMap F K b)).ker := hq
  have hm := ConjugationQuaternion.quaternionUnitNorm_ker_le_commutator (algebraMap F K a) (algebraMap F K b)
    ((map_ne_zero (algebraMap F K)).mpr ha) ((map_ne_zero (algebraMap F K)).mpr hb) hn
  have hle : (commutator ℍ[K,algebraMap F K a,algebraMap F K b]ˣ).map e.toMonoidHom ≤
      commutator (localQuaternionModel F K a b)ˣ := by
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  have he := hle (Subgroup.mem_map_of_mem e.toMonoidHom hm)
  change e (e.symm q) ∈ commutator (localQuaternionModel F K a b)ˣ at he
  simpa only [MulEquiv.apply_symm_apply] using he

end

/-! Weak approximation at arbitrary finite sets of finite places for
the reduced-norm-one group of every nondegenerate quaternion algebra. -/

open scoped Classical _root_.NumberField _root_.Quaternion
open IsDedekindDomain QuaternionAlgebra

variable {F : Type} [Field F] [NumberField F]
  {ι : Type*} [Fintype ι] (v : ι → HeightOneSpectrum (𝓞 F)) (a b : F)

theorem denseRange_localQuaternionUnits (hv : Function.Injective v) :
    DenseRange (fun q : ℍ[F,a,b]ˣ => fun i => localQuaternionUnitMap F ((v i).adicCompletion F) a b q) := by
  exact FiniteAlgebraApproximation.denseRange_finiteAlgebraUnits_of_bases v hv
    (fun i => localQuaternionCoefficients F ((v i).adicCompletion F) a b)
    (fun i => localQuaternionCoefficients_injective F ((v i).adicCompletion F) a b)
    (basisOneIJK a 0 b) (fun i => localQuaternionBasis F ((v i).adicCompletion F) a b)
    (fun i j => localQuaternionBasis_apply F ((v i).adicCompletion F) a b j)

def quaternionNormOneDiagonal :
    (Norm.quaternionUnitNorm a b).ker →*
      (∀ i, (localQuaternionUnitNorm F ((v i).adicCompletion F) a b).ker) :=
  CharacterKernelApproximation.characterKernelPiDiagonal (fun i => localQuaternionUnitMap F ((v i).adicCompletion F) a b)
    (Norm.quaternionUnitNorm a b) (fun i => localQuaternionUnitNorm F ((v i).adicCompletion F) a b)
    (LocalAlgebraUnitsDensity.finiteCompletionUnitMap v)
    (fun i q => localQuaternionUnitNorm_map F ((v i).adicCompletion F) a b q)

theorem denseRange_quaternionNormOneDiagonal (hv : Function.Injective v) (ha : a ≠ 0) (hb : b ≠ 0) :
    DenseRange (quaternionNormOneDiagonal v a b) := by
  apply CharacterKernelApproximation.denseRange_characterKernelPiDiagonal
    (fun i => localQuaternionUnitMap F ((v i).adicCompletion F) a b)
    (denseRange_localQuaternionUnits v a b hv) (Norm.quaternionUnitNorm a b)
    (fun i => localQuaternionUnitNorm F ((v i).adicCompletion F) a b)
    (LocalAlgebraUnitsDensity.finiteCompletionUnitMap v)
    (fun i q => localQuaternionUnitNorm_map F ((v i).adicCompletion F) a b q)
  intro i
  let : CharZero ((v i).adicCompletion F) :=
    charZero_of_injective_ringHom (algebraMap F ((v i).adicCompletion F)).injective
  exact localQuaternionUnitNorm_ker_le_commutator F ((v i).adicCompletion F) a b ha hb

end

end OAI.NumberTheory.Quaternion.Arithmetic.LocalModel
