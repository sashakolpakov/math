import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.Hermitian
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-! # Special Linear -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.SpecialLinear

noncomputable section

/-! Norm-one quaternions give determinant-one binary matrices in the
specified quadratic coordinates. Over a field containing the nonzero
quadratic root these matrices fill SL₂. -/

open scoped Classical _root_.Quaternion _root_.Matrix
open QuaternionAlgebra _root_.Matrix

section NormOne
variable {F E : Type*} [Field F] [CommRing E] [Algebra F E]
  (a b : F) (δ : E) (hδ : δ ^ 2 = algebraMap F E a)

def unitaryQuaternionNormOneHom :
    (NumberTheory.Quaternion.Arithmetic.Norm.quaternionUnitNorm a (-b)).ker →* Matrix.SpecialLinearGroup (Fin 2) E where
  toFun q := ⟨UnitaryMatrix.unitaryQuaternionMap a b δ hδ q.val.val,
    (UnitaryMatrix.unitaryQuaternionMap_det a b δ hδ q.val.val).trans
      ((congrArg (algebraMap F E) (congrArg Units.val (MonoidHom.mem_ker.mp q.property))).trans
        (map_one (algebraMap F E)))⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (UnitaryMatrix.unitaryQuaternionMap a b δ hδ)
  map_mul' q r := by
    apply Subtype.ext
    exact map_mul (UnitaryMatrix.unitaryQuaternionMap a b δ hδ) q.val.val r.val.val

theorem unitaryQuaternionNormOneHom_gram [StarRing E]
    (hreal : ∀ t : F, star (algebraMap F E t) = algebraMap F E t)
    (hstar : star δ = -δ) (q : (NumberTheory.Quaternion.Arithmetic.Norm.quaternionUnitNorm a (-b)).ker) :
    (unitaryQuaternionNormOneHom a b δ hδ q).val.conjTranspose *
        Hermitian.binaryHermitianForm (algebraMap F E b) * (unitaryQuaternionNormOneHom a b δ hδ q).val =
      Hermitian.binaryHermitianForm (algebraMap F E b) := by
  change (UnitaryMatrix.unitaryQuaternionMap a b δ hδ q.val.val).conjTranspose * _ *
    UnitaryMatrix.unitaryQuaternionMap a b δ hδ q.val.val = _
  have hn : NumberTheory.Quaternion.Arithmetic.Norm.quaternionNorm a (-b) q.val.val = 1 :=
    congrArg Units.val (MonoidHom.mem_ker.mp q.property)
  rw [Hermitian.unitaryQuaternionMap_gram a b δ hδ hreal hstar, hn, map_one, one_smul]

end NormOne

variable {K : Type*} [Field K] [CharZero K]
  (a b δ : K) (hδ : δ ^ 2 = algebraMap K K a) (hb : b ≠ 0) (hδ0 : δ ≠ 0)

def unitaryQuaternionInverse (M : Matrix (Fin 2) (Fin 2) K) : ℍ[K,a,-b] :=
  ⟨(M 0 0 + M 1 1) / 2, (M 0 0 - M 1 1) / (2 * δ),
    (M 1 0 - M 0 1 / b) / 2, -(M 1 0 + M 0 1 / b) / (2 * δ)⟩

include hb hδ0 in
theorem unitaryQuaternionInverse_apply (M : Matrix (Fin 2) (Fin 2) K) :
    UnitaryMatrix.unitaryQuaternionMap a b δ hδ (unitaryQuaternionInverse a b δ M) = M := by
  rw [UnitaryMatrix.unitaryQuaternionMap_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitaryQuaternionInverse] <;> field_simp [hb, hδ0] <;> ring

include hb hδ0 in
theorem unitaryQuaternionNormOneHom_surjective :
    Function.Surjective (unitaryQuaternionNormOneHom a b δ hδ) := by
  intro M
  let q := unitaryQuaternionInverse a b δ M.val
  have he : UnitaryMatrix.unitaryQuaternionMap a b δ hδ q = M.val :=
    unitaryQuaternionInverse_apply a b δ hδ hb hδ0 M.val
  have hn : NumberTheory.Quaternion.Arithmetic.Norm.quaternionNorm a (-b) q = 1 := by
    have hd := (UnitaryMatrix.unitaryQuaternionMap_det a b δ hδ q).symm.trans
      ((congrArg Matrix.det he).trans M.property)
    simpa only [Algebra.algebraMap_self, RingHom.id_apply] using hd
  let u := NumberTheory.Quaternion.Arithmetic.Norm.quaternionUnitOfNormNeZero a (-b) q (hn ▸ one_ne_zero)
  have hu : u ∈ (NumberTheory.Quaternion.Arithmetic.Norm.quaternionUnitNorm a (-b)).ker := by
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    exact hn
  exact ⟨⟨u, hu⟩, Subtype.ext he⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.SpecialLinear
