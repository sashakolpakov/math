import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters

/-! # Scalar Conjugate -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.ScalarConjugate.CM.Extension

/-! Actual scalar extension of algebraic Hecke operators. It is a ring
homomorphism, so projector identities and annihilating polynomials are
preserved. The tensor associativity map identifies iterated scalar
extension with the original complexified rational cohomology. -/

open scoped Classical TensorProduct
open TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors

variable (A : IntermediateField ℚ ℂ)
  (U : Type*) [AddCommGroup U] [Module ℚ U]

def extendEnd :
    Module.End A (A ⊗[ℚ] U) →+* Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification U) :=
  (AlgebraTensorModule.cancelBaseChange ℚ A ℂ ℂ U).conjRingEquiv.toRingHom.comp
    (Module.End.baseChangeHom A ℂ (A ⊗[ℚ] U)).toRingHom

theorem cancel_one_tmul (x : A ⊗[ℚ] U) :
    AlgebraTensorModule.cancelBaseChange ℚ A ℂ ℂ U ((1 : ℂ) ⊗ₜ[A] x) =
      ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion A U x := by
  induction x using TensorProduct.inductionOn with
  | tmul a u => simp [AlgebraTensorModule.cancelBaseChange_tmul,
      ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion_tmul, Algebra.smul_def]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

theorem extendEnd_apply_inclusion (Q : Module.End A (A ⊗[ℚ] U)) (x : A ⊗[ℚ] U) :
    extendEnd A U Q (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion A U x) = ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion A U (Q x) := by
  let e := AlgebraTensorModule.cancelBaseChange ℚ A ℂ ℂ U
  change e (Q.baseChange ℂ (e.symm (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion A U x))) = _
  rw [← cancel_one_tmul A U x, e.symm_apply_apply,
    LinearMap.baseChange_tmul, cancel_one_tmul]

/-- The included coefficient vectors span complexified rational cohomology. -/
theorem end_ext_on_inclusion (P Q : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification U))
    (h : ∀ x : A ⊗[ℚ] U,
      P (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion A U x) = Q (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion A U x)) : P = Q := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a u =>
      have hu := h ((1 : A) ⊗ₜ[ℚ] u)
      simp only [ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion_tmul, IntermediateField.coe_one] at hu
      have ha := congrArg (fun z : ComplexMultiplication.WeightOne.CM.Complexification U => a • z) hu
      simpa only [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one] using ha

theorem extendEnd_scalar (a : A) :
    extendEnd A U (a • 1) = (a : ℂ) • 1 := by
  apply end_ext_on_inclusion A U
  intro x
  rw [extendEnd_apply_inclusion, LinearMap.smul_apply, Module.End.one_apply,
    ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion_smul, LinearMap.smul_apply, Module.End.one_apply]

/-- Two successive coefficient extensions agree with the direct one. -/
theorem extendEnd_rational (T : Module.End ℚ U) :
    extendEnd A U (T.baseChange A) = T.baseChange ℂ := by
  apply end_ext_on_inclusion A U
  intro x
  rw [extendEnd_apply_inclusion, ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion_baseChange]

theorem extendEnd_eq_complexHom [FiniteDimensional ℚ U]
    (Q : Module.End A (A ⊗[ℚ] U)) :
    extendEnd A U Q = ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients A U U
      ((ComplexMultiplication.HomBaseChange.CM.homBaseChangeEquiv A U U).symm Q) := by
  apply end_ext_on_inclusion A U
  intro x
  rw [extendEnd_apply_inclusion, ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients_apply_inclusion]
  congr 1
  exact (LinearMap.congr_fun ((ComplexMultiplication.HomBaseChange.CM.homBaseChangeEquiv A U U).apply_symm_apply Q) x).symm

/-- Scalar extension carries actual generalized eigenvectors to their
corresponding complex generalized eigenvectors. -/
theorem inclusion_mem_genEigenspace
    (T : Module.End A (A ⊗[ℚ] U)) (a : A) (k : ℕ∞)
    {x : A ⊗[ℚ] U} (hx : x ∈ T.genEigenspace a k) :
    ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion A U x ∈ (extendEnd A U T).genEigenspace (a : ℂ) k := by
  obtain ⟨n, hn, hx⟩ := Module.End.mem_genEigenspace.mp hx
  refine Module.End.mem_genEigenspace.mpr ⟨n, hn, ?_⟩
  change ((extendEnd A U T - (a : ℂ) • 1) ^ n) (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion A U x) = 0
  have hdiff : extendEnd A U (T - a • 1) = extendEnd A U T - (a : ℂ) • 1 := by
    rw [map_sub (extendEnd A U) T (a • 1), extendEnd_scalar]
  have heq := congrArg (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion A U) (LinearMap.mem_ker.mp hx)
  rw [map_zero, ← extendEnd_apply_inclusion, map_pow, hdiff] at heq
  exact heq

theorem inclusion_mem_jointSpace {J : Type*}
    (T : J → Module.End A (A ⊗[ℚ] U)) (χ : J → A)
    {x : A ⊗[ℚ] U} (hx : x ∈ HeckeCharacters.CM.Projectors.jointSpace T χ) :
    ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion A U x ∈
      HeckeCharacters.CM.Projectors.jointSpace (fun j => extendEnd A U (T j)) (fun j => (χ j : ℂ)) := by
  simp only [HeckeCharacters.CM.Projectors.jointSpace, Submodule.mem_iInf] at hx ⊢
  intro j
  exact inclusion_mem_genEigenspace A U (T j) (χ j) ⊤ (hx j)

theorem range_extendEnd [FiniteDimensional ℚ U]
    (Q : Module.End A (A ⊗[ℚ] U)) :
    LinearMap.range (extendEnd A U Q) = CMExtraction.Definitions.CM.conjugateSpace A (LinearMap.range Q) 1 := by
  rw [extendEnd_eq_complexHom, Coefficients.CM.extended_range_eq_conjugateSpace]
  have heq : ComplexMultiplication.HomBaseChange.CM.homBaseChange A U U ((ComplexMultiplication.HomBaseChange.CM.homBaseChangeEquiv A U U).symm Q) = Q :=
    (ComplexMultiplication.HomBaseChange.CM.homBaseChangeEquiv A U U).apply_symm_apply Q
  rw [heq]

variable {I J : Type*} [DecidableEq I]
  (T : J → Module.End A (A ⊗[ℚ] U))
  (χ : I → J → A)
  (hS : DirectSum.IsInternal (fun i => HeckeCharacters.CM.Projectors.jointSpace T (χ i)))

def extendedProjector (i : I) : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification U) :=
  extendEnd A U (HeckeCharacters.CM.Projectors.projector (fun j => HeckeCharacters.CM.Projectors.jointSpace T (χ j)) hS i)

theorem extendedProjector_range_le [FiniteDimensional ℚ U] (i : I) :
    LinearMap.range (extendedProjector A U T χ hS i) ≤
      HeckeCharacters.CM.Projectors.jointSpace (fun j => extendEnd A U (T j)) (fun j => (χ i j : ℂ)) := by
  rw [extendedProjector, range_extendEnd, HeckeCharacters.CM.Projectors.projector_range]
  apply Submodule.span_le.mpr
  rintro y ⟨x, hx, rfl⟩
  rw [Coefficients.CM.scalarConjugate_identity]
  exact inclusion_mem_jointSpace A U T (χ i) hx

theorem sum_extendedProjector [Fintype I] (x : ComplexMultiplication.WeightOne.CM.Complexification U) :
    ∑ i, extendedProjector A U T χ hS i x = x := by
  have hs : ∑ i, HeckeCharacters.CM.Projectors.projector (fun j => HeckeCharacters.CM.Projectors.jointSpace T (χ j)) hS i = 1 := by
    apply LinearMap.ext
    intro y
    simpa only [LinearMap.sum_apply, Module.End.one_apply] using
      HeckeCharacters.CM.Projectors.sum_projector (fun j => HeckeCharacters.CM.Projectors.jointSpace T (χ j)) hS y
  have h := congrArg (extendEnd A U) hs
  rw [map_sum, map_one] at h
  simpa only [extendedProjector, LinearMap.sum_apply, Module.End.one_apply]
    using LinearMap.congr_fun h x

theorem extendedProjector_commutes [Fintype I]
    (hcomm : ∀ j k, Commute (T j) (T k)) (i : I) (j : J) :
    Commute (extendedProjector A U T χ hS i) (extendEnd A U (T j)) := by
  have hp := HeckeCharacters.CM.Projectors.projector_commutes (fun k => HeckeCharacters.CM.Projectors.jointSpace T (χ k)) hS (T j)
    (fun k x hx => HeckeCharacters.CM.Projectors.jointSpace_stable_of_commutes T (χ k) (T j)
      (fun k => hcomm k j) hx) i
  change extendEnd A U _ * extendEnd A U _ = extendEnd A U _ * extendEnd A U _
  rw [← map_mul, ← map_mul, hp.eq]

theorem extendedProjector_range [FiniteDimensional ℚ U] [Fintype I]
    (hcomm : ∀ j k, Commute (T j) (T k)) (hχ : Function.Injective χ) (i : I) :
    LinearMap.range (extendedProjector A U T χ hS i) =
      HeckeCharacters.CM.Projectors.jointSpace (fun j => extendEnd A U (T j)) (fun j => (χ i j : ℂ)) := by
  apply HeckeCharacters.CM.Projectors.ranges_eq_jointSpaces
    (fun j => extendEnd A U (T j)) (fun i j => (χ i j : ℂ))
    (fun i j hij => hχ (funext fun k => Subtype.ext (congrFun hij k)))
    (extendedProjector A U T χ hS)
    (sum_extendedProjector A U T χ hS)
    (extendedProjector_range_le A U T χ hS)
    (extendedProjector_commutes A U T χ hS hcomm) i

/-- The extended algebraic projectors are the canonical complex spectral
projectors and hence preserve the genuine Hodge grading. -/
theorem extendedProjector_hodge [FiniteDimensional ℚ U] [Fintype I]
    (hcomm : ∀ j k, Commute (T j) (T k)) (hχ : Function.Injective χ)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U)
    (hHodge : ∀ j, extendEnd A U (T j) ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H) (i : I) :
    extendedProjector A U T χ hS i ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H := by
  let TC := fun j => extendEnd A U (T j)
  let χC := fun i j => (χ i j : ℂ)
  let SC := fun i => HeckeCharacters.CM.Projectors.jointSpace TC (χC i)
  let P := extendedProjector A U T χ hS
  have hinj : Function.Injective χC :=
    fun i j hij => hχ (funext fun k => Subtype.ext (congrFun hij k))
  have hTC : ∀ j k, Commute (TC j) (TC k) := by
    intro j k
    change extendEnd A U (T j) * extendEnd A U (T k) =
      extendEnd A U (T k) * extendEnd A U (T j)
    rw [← map_mul, ← map_mul, (hcomm j k).eq]
  have hfull : iSupIndep (HeckeCharacters.CM.Projectors.jointSpace TC) :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo TC
      (fun j k => Module.End.mapsTo_maxGenEigenspace_of_comm (hTC k j).eq)
  have hSC : DirectSum.IsInternal SC := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (hfull.comp hinj)
    apply top_unique
    intro x _
    rw [← sum_extendedProjector A U T χ hS x]
    exact Submodule.sum_mem _ (fun j _ =>
      (le_iSup SC j) (extendedProjector_range_le A U T χ hS j
        (LinearMap.mem_range_self (P j) x)))
  have hr : ∀ j, LinearMap.range (P j) = SC j :=
    extendedProjector_range A U T χ hS hcomm hχ
  have hid : ∀ j, P j * P j = P j := by
    intro j
    have ha : HeckeCharacters.CM.Projectors.projector (fun k => HeckeCharacters.CM.Projectors.jointSpace T (χ k)) hS j *
        HeckeCharacters.CM.Projectors.projector (fun k => HeckeCharacters.CM.Projectors.jointSpace T (χ k)) hS j =
          HeckeCharacters.CM.Projectors.projector (fun k => HeckeCharacters.CM.Projectors.jointSpace T (χ k)) hS j :=
      HeckeCharacters.CM.Projectors.projector_idempotent (fun k => HeckeCharacters.CM.Projectors.jointSpace T (χ k)) hS j
    exact (map_mul (extendEnd A U) _ _).symm.trans (congrArg (extendEnd A U) ha)
  have horth : ∀ j k, k ≠ j → P j * P k = 0 := by
    intro j k hkj
    have ha := congrArg (extendEnd A U)
      (HeckeCharacters.CM.Projectors.projector_mul_ne (fun k => HeckeCharacters.CM.Projectors.jointSpace T (χ k)) hS hkj)
    simpa only [P, extendedProjector, map_mul, map_zero] using ha
  have hp : P i = HeckeCharacters.CM.Projectors.projector SC hSC i := by
    apply HeckeCharacters.CM.Projectors.projector_unique SC hSC i (P i)
    · intro x hx
      rw [← hr i] at hx
      obtain ⟨y, rfl⟩ := hx
      exact LinearMap.congr_fun (hid i) y
    · intro j hji x hx
      rw [← hr j] at hx
      obtain ⟨y, rfl⟩ := hx
      exact LinearMap.congr_fun (horth i j hji) y
  change P i ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H
  rw [hp]
  exact HeckeCharacters.CM.Projectors.joint_projector_hodge H TC χC hSC hHodge i

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.ScalarConjugate.CM.Extension

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.ScalarConjugate.CM.Projectors

/-!
# Actual scalar conjugates of coefficient projectors

Conjugating a Hom tensor conjugates its image. Thus CMExtraction's conjugateSpace
is the range of the conjugated operator, on the same complex vector space.
Nonvanishing and idempotence survive this operation.
-/

open scoped Classical TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ScalarConjugate.CM.Extension

variable (K : IntermediateField ℚ ℂ)
variable {U : Type*} [AddCommGroup U] [Module ℚ U]

theorem coefficientInclusion_injective : Function.Injective (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K U) :=
  Module.Flat.rTensor_preserves_injective_linearMap K.val.toLinearMap K.val.injective

theorem scalarConjugate_mul (σ τ : Gal(K/ℚ)) (x : K ⊗[ℚ] U) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K U σ (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K U τ x) =
      ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K U (σ * τ) x := by
  induction x using TensorProduct.inductionOn with
  | tmul a u => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem scalarConjugate_inverse (σ : Gal(K/ℚ)) (x : K ⊗[ℚ] U) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K U σ (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K U σ⁻¹ x) = x := by
  rw [scalarConjugate_mul, mul_inv_cancel, Coefficients.CM.scalarConjugate_identity]

theorem scalarConjugate_injective (σ : Gal(K/ℚ)) :
    Function.Injective (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K U σ) := by
  intro x y h
  have h' := congrArg (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K U σ⁻¹) h
  simpa only [scalarConjugate_mul, inv_mul_cancel, Coefficients.CM.scalarConjugate_identity] using h'

theorem complexHomOfCoefficients_injective [FiniteDimensional ℚ U] :
    Function.Injective (ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K U U) :=
  (ComplexMultiplication.HomBaseChange.CM.homBaseChange_bijective ℂ U U).1.comp (coefficientInclusion_injective K)

/-- Scalar conjugation acts on the coefficient image by the actual tensor map. -/
theorem conjugated_range_generators
    (p : K ⊗[ℚ] (U →ₗ[ℚ] U)) (σ : Gal(K/ℚ)) :
    {z | ∃ x ∈ LinearMap.range (ComplexMultiplication.HomBaseChange.CM.homBaseChange K U U p),
      z = ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K U (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K U σ x)} =
    {z | ∃ x ∈ LinearMap.range
        (ComplexMultiplication.HomBaseChange.CM.homBaseChange K U U (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K (U →ₗ[ℚ] U) σ p)),
      z = ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K U x} := by
  ext z
  constructor
  · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
    refine ⟨_, ⟨ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K U σ y, ?_⟩, rfl⟩
    exact ComplexMultiplication.HomBaseChange.CM.homBaseChange_scalarConjugate K U U σ p y
  · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
    refine ⟨ComplexMultiplication.HomBaseChange.CM.homBaseChange K U U p (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K U σ⁻¹ y),
      ⟨_, rfl⟩, ?_⟩
    rw [← ComplexMultiplication.HomBaseChange.CM.homBaseChange_scalarConjugate, scalarConjugate_inverse]

/-- All conjugate spaces in CMExtraction are ranges on the fixed complex fiber. -/
theorem conjugated_range_eq_conjugateSpace
    (p : K ⊗[ℚ] (U →ₗ[ℚ] U)) (σ : Gal(K/ℚ)) :
    LinearMap.range
        (ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K U U (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K (U →ₗ[ℚ] U) σ p)) =
      CMExtraction.Definitions.CM.conjugateSpace K (LinearMap.range (ComplexMultiplication.HomBaseChange.CM.homBaseChange K U U p)) σ := by
  rw [Coefficients.CM.extended_range_eq_conjugateSpace]
  unfold CMExtraction.Definitions.CM.conjugateSpace
  simp only [Coefficients.CM.scalarConjugate_identity]
  rw [conjugated_range_generators]

theorem conjugateSpace_ne_bot [FiniteDimensional ℚ U]
    (p : K ⊗[ℚ] (U →ₗ[ℚ] U)) (σ : Gal(K/ℚ))
    (hne : ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K U U p ≠ 0) :
    CMExtraction.Definitions.CM.conjugateSpace K (LinearMap.range (ComplexMultiplication.HomBaseChange.CM.homBaseChange K U U p)) σ ≠ ⊥ := by
  rw [← conjugated_range_eq_conjugateSpace]
  intro h
  have hz := LinearMap.range_eq_bot.mp h
  have hp : ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K (U →ₗ[ℚ] U) σ p = 0 :=
    complexHomOfCoefficients_injective K (by simpa only [map_zero] using hz)
  have hp' : p = 0 := scalarConjugate_injective K σ (by simpa only [map_zero] using hp)
  exact hne (by rw [hp', map_zero])

theorem coefficient_projector_idempotent
    (p : K ⊗[ℚ] (U →ₗ[ℚ] U))
    (hp : IsIdempotentElem (ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K U U p)) :
    IsIdempotentElem (ComplexMultiplication.HomBaseChange.CM.homBaseChange K U U p) := by
  apply LinearMap.ext
  intro x
  apply coefficientInclusion_injective K
  have he := LinearMap.congr_fun hp (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K U x)
  simpa only [Module.End.mul_apply, ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients_apply_inclusion] using he

theorem conjugated_projector_idempotent
    (p : K ⊗[ℚ] (U →ₗ[ℚ] U)) (σ : Gal(K/ℚ))
    (hp : IsIdempotentElem (ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K U U p)) :
    IsIdempotentElem
      (ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K U U (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K (U →ₗ[ℚ] U) σ p)) := by
  let Q := ComplexMultiplication.HomBaseChange.CM.homBaseChange K U U p
  let Qσ := ComplexMultiplication.HomBaseChange.CM.homBaseChange K U U (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K (U →ₗ[ℚ] U) σ p)
  have hQ := coefficient_projector_idempotent K p hp
  have hQσ : Qσ * Qσ = Qσ := by
    apply LinearMap.ext
    intro x
    have hx : x = ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K U σ (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K U σ⁻¹ x) :=
      (scalarConjugate_inverse K σ x).symm
    rw [hx]
    change Qσ (Qσ _) = Qσ _
    simp only [Qσ, ComplexMultiplication.HomBaseChange.CM.homBaseChange_scalarConjugate]
    exact congrArg (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K U σ)
      (LinearMap.congr_fun hQ (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K U σ⁻¹ x))
  apply Extension.end_ext_on_inclusion K U
  intro x
  change ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K U U _ (ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K U U _ _) = _
  simp only [ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients_apply_inclusion]
  exact congrArg (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K U) (LinearMap.congr_fun hQσ x)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.ScalarConjugate.CM.Projectors

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.ScalarConjugate.CM.SpectralConjugation

/-! Scalar automorphisms permute the simultaneous generalized eigenspaces
of a rational action. Their coordinate projections therefore remain Hodge
compatible after extension to the fixed complex fiber. -/

open scoped Classical TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ScalarConjugate.CM.Extension
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ScalarConjugate.CM.Projectors

variable (A : IntermediateField ℚ ℂ)
  (U : Type*) [AddCommGroup U] [Module ℚ U]

/-- Conjugate both input and output coefficients, leaving the rational
cohomology factor fixed. Semilinearity cancels, giving an A-linear map. -/
def twistEnd (σ : Gal(A/ℚ)) (Q : Module.End A (A ⊗[ℚ] U)) :
    Module.End A (A ⊗[ℚ] U) where
  toFun x := ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ A U σ (Q (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ A U σ⁻¹ x))
  map_add' x y := by simp only [map_add]
  map_smul' a x := by
    simp only [ComplexMultiplication.ScalarDescent.CM.scalarConjugate_smul, map_smul, RingHom.id_apply]
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

theorem twistEnd_apply_conjugate (σ : Gal(A/ℚ))
    (Q : Module.End A (A ⊗[ℚ] U)) (x : A ⊗[ℚ] U) :
    twistEnd A U σ Q (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ A U σ x) =
      ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ A U σ (Q x) := by
  change ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ A U σ (Q _) = _
  rw [Projectors.scalarConjugate_mul, inv_mul_cancel, Coefficients.CM.scalarConjugate_identity]

theorem twistEnd_homTensor [FiniteDimensional ℚ U]
    (σ : Gal(A/ℚ)) (Q : Module.End A (A ⊗[ℚ] U)) :
    ComplexMultiplication.HomBaseChange.CM.homBaseChange A U U (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ A (U →ₗ[ℚ] U) σ
      ((ComplexMultiplication.HomBaseChange.CM.homBaseChangeEquiv A U U).symm Q)) = twistEnd A U σ Q := by
  apply LinearMap.ext
  intro x
  have hx := Projectors.scalarConjugate_inverse A σ x
  conv_lhs => rw [← hx]
  rw [ComplexMultiplication.HomBaseChange.CM.homBaseChange_scalarConjugate]
  change ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ A U σ _ = ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ A U σ (Q _)
  congr 1
  exact LinearMap.congr_fun ((ComplexMultiplication.HomBaseChange.CM.homBaseChangeEquiv A U U).apply_symm_apply Q) _

theorem scalarConjugate_shift_power (σ : Gal(A/ℚ)) (T : Module.End ℚ U)
    (a : A) (n : ℕ) (x : A ⊗[ℚ] U) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ A U σ (((T.baseChange A - a • 1) ^ n) x) =
      ((T.baseChange A - σ a • 1) ^ n) (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ A U σ x) := by
  induction n with
  | zero => simp only [pow_zero, Module.End.one_apply]
  | succ n hn =>
    simp only [pow_succ', Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, map_sub,
      ComplexMultiplication.EmbeddingCoefficientField.CM.scalarConjugate_baseChange, ComplexMultiplication.ScalarDescent.CM.scalarConjugate_smul, hn]

theorem scalarConjugate_mem_jointSpace {J : Type*}
    (T : J → Module.End ℚ U) (χ : J → A) (σ : Gal(A/ℚ))
    {x : A ⊗[ℚ] U} (hx : x ∈ HeckeCharacters.CM.Projectors.jointSpace (fun j => (T j).baseChange A) χ) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ A U σ x ∈
      HeckeCharacters.CM.Projectors.jointSpace (fun j => (T j).baseChange A) (fun j => σ (χ j)) := by
  simp only [HeckeCharacters.CM.Projectors.jointSpace, Submodule.mem_iInf] at hx ⊢
  intro j
  obtain ⟨n, hn, hx⟩ := Module.End.mem_genEigenspace.mp (hx j)
  refine Module.End.mem_genEigenspace.mpr ⟨n, hn, ?_⟩
  change (((T j).baseChange A - σ (χ j) • 1) ^ n)
    (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ A U σ x) = 0
  rw [← scalarConjugate_shift_power, LinearMap.mem_ker.mp hx, map_zero]

variable {I J : Type*} [Fintype I] [DecidableEq I]
  (T : J → Module.End ℚ U) (hcomm : ∀ j k, Commute (T j) (T k))
  (χ : I → J → A) (hχ : Function.Injective χ)
  (hS : DirectSum.IsInternal (fun i => HeckeCharacters.CM.Projectors.jointSpace (fun j => (T j).baseChange A) (χ i)))

include hcomm hχ hS

theorem conjugate_joint_internal (σ : Gal(A/ℚ)) :
    DirectSum.IsInternal
      (fun i => HeckeCharacters.CM.Projectors.jointSpace (fun j => (T j).baseChange A) (fun j => σ (χ i j))) := by
  let TA := fun j => (T j).baseChange A
  let S := fun i => HeckeCharacters.CM.Projectors.jointSpace TA (χ i)
  let Sσ := fun i => HeckeCharacters.CM.Projectors.jointSpace TA (fun j => σ (χ i j))
  have hTA : ∀ j k, Commute (TA j) (TA k) := by
    intro j k
    change (T j).baseChange A * (T k).baseChange A =
      (T k).baseChange A * (T j).baseChange A
    simpa only [LinearMap.baseChange_mul] using
      congrArg (fun f : Module.End ℚ U => f.baseChange A) (hcomm j k).eq
  have hi : iSupIndep (HeckeCharacters.CM.Projectors.jointSpace TA) :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo TA
      (fun j k => Module.End.mapsTo_maxGenEigenspace_of_comm (hTA k j).eq)
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (hi.comp (fun i k hik => hχ (funext fun j => σ.injective (congrFun hik j))))
  apply top_unique
  intro x _
  have heq : x = ∑ i, ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ A U σ
      (HeckeCharacters.CM.Projectors.projector S hS i (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ A U σ⁻¹ x)) := by
    rw [← map_sum, HeckeCharacters.CM.Projectors.sum_projector, Projectors.scalarConjugate_inverse]
  rw [heq]
  exact Submodule.sum_mem _ (fun i _ => (le_iSup Sσ i)
    (scalarConjugate_mem_jointSpace A U T (χ i) σ (HeckeCharacters.CM.Projectors.projector_mem S hS i _)))

theorem twist_projector (σ : Gal(A/ℚ)) (i : I) :
    twistEnd A U σ
      (HeckeCharacters.CM.Projectors.projector (fun i => HeckeCharacters.CM.Projectors.jointSpace (fun j => (T j).baseChange A) (χ i)) hS i) =
    HeckeCharacters.CM.Projectors.projector (fun i => HeckeCharacters.CM.Projectors.jointSpace (fun j => (T j).baseChange A) (fun j => σ (χ i j)))
      (conjugate_joint_internal A U T hcomm χ hχ hS σ) i := by
  let S := fun i => HeckeCharacters.CM.Projectors.jointSpace (fun j => (T j).baseChange A) (χ i)
  have hinv : ∀ j x,
      x ∈ HeckeCharacters.CM.Projectors.jointSpace (fun k => (T k).baseChange A) (fun k => σ (χ j k)) →
        ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ A U σ⁻¹ x ∈ S j := by
    intro j x hx
    have he := scalarConjugate_mem_jointSpace A U T (fun k => σ (χ j k)) σ⁻¹ hx
    simpa only [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply] using he
  apply HeckeCharacters.CM.Projectors.projector_unique
  · intro x hx
    change ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ A U σ (HeckeCharacters.CM.Projectors.projector S hS i _) = x
    rw [HeckeCharacters.CM.Projectors.projector_of_mem S hS i (hinv i x hx), Projectors.scalarConjugate_inverse]
  · intro j hji x hx
    change ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ A U σ (HeckeCharacters.CM.Projectors.projector S hS i _) = 0
    rw [HeckeCharacters.CM.Projectors.projector_of_mem_ne S hS hji (hinv j x hx), map_zero]

/-- Galois conjugation preserves the Hodge compatibility of spectral
projectors because it changes their joint eigenvalues for the rational action. -/
theorem conjugated_spectral_projector_hodge [FiniteDimensional ℚ U]
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (hHodge : ∀ j, ComplexMultiplication.WeightOne.CM.IsHodgeMap H H (T j))
    (σ : Gal(A/ℚ)) (i : I) :
    ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients A U U (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ A (U →ₗ[ℚ] U) σ
      ((ComplexMultiplication.HomBaseChange.CM.homBaseChangeEquiv A U U).symm
        (HeckeCharacters.CM.Projectors.projector (fun i => HeckeCharacters.CM.Projectors.jointSpace (fun j => (T j).baseChange A) (χ i)) hS i)))
      ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H := by
  have heq : ∀ p : A ⊗[ℚ] (U →ₗ[ℚ] U),
      ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients A U U p = Extension.extendEnd A U (ComplexMultiplication.HomBaseChange.CM.homBaseChange A U U p) := by
    intro p
    rw [Extension.extendEnd_eq_complexHom]
    congr 1
    exact ((ComplexMultiplication.HomBaseChange.CM.homBaseChangeEquiv A U U).symm_apply_apply p).symm
  rw [heq, twistEnd_homTensor, twist_projector A U T hcomm χ hχ hS]
  apply Extension.extendedProjector_hodge A U (fun j => (T j).baseChange A)
    (fun i j => σ (χ i j)) (conjugate_joint_internal A U T hcomm χ hχ hS σ)
  · intro j k
    change (T j).baseChange A * (T k).baseChange A =
      (T k).baseChange A * (T j).baseChange A
    simpa only [LinearMap.baseChange_mul] using
      congrArg (fun f : Module.End ℚ U => f.baseChange A) (hcomm j k).eq
  · intro j k hjk
    exact hχ (funext fun l => σ.injective (congrFun hjk l))
  · intro j
    rw [Extension.extendEnd_rational]
    exact (ComplexMultiplication.Hodge.MapDescent.CM.baseChange_mem_hodgeHomSubspace_iff H H (T j)).mpr (hHodge j)

theorem conjugated_spectral_projector_range [FiniteDimensional ℚ U]
    (σ : Gal(A/ℚ)) (i : I) :
    LinearMap.range
      (ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients A U U (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ A (U →ₗ[ℚ] U) σ
        ((ComplexMultiplication.HomBaseChange.CM.homBaseChangeEquiv A U U).symm
          (HeckeCharacters.CM.Projectors.projector (fun i => HeckeCharacters.CM.Projectors.jointSpace (fun j => (T j).baseChange A) (χ i)) hS i)))) =
      HeckeCharacters.CM.Projectors.jointSpace (fun j => (T j).baseChange ℂ) (fun j => (σ (χ i j) : ℂ)) := by
  have heq : ∀ p : A ⊗[ℚ] (U →ₗ[ℚ] U),
      ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients A U U p = Extension.extendEnd A U (ComplexMultiplication.HomBaseChange.CM.homBaseChange A U U p) := by
    intro p
    rw [Extension.extendEnd_eq_complexHom]
    congr 1
    exact ((ComplexMultiplication.HomBaseChange.CM.homBaseChangeEquiv A U U).symm_apply_apply p).symm
  rw [heq, twistEnd_homTensor, twist_projector A U T hcomm χ hχ hS]
  have hTA : ∀ j k, Commute ((T j).baseChange A) ((T k).baseChange A) := by
    intro j k
    change (T j).baseChange A * (T k).baseChange A =
      (T k).baseChange A * (T j).baseChange A
    simpa only [LinearMap.baseChange_mul] using
      congrArg (fun f : Module.End ℚ U => f.baseChange A) (hcomm j k).eq
  have hr := Extension.extendedProjector_range A U (fun j => (T j).baseChange A)
    (fun i j => σ (χ i j)) (conjugate_joint_internal A U T hcomm χ hχ hS σ)
    hTA (fun j k hjk => hχ (funext fun l => σ.injective (congrFun hjk l))) i
  simpa only [Extension.extendedProjector, Extension.extendEnd_rational] using hr

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.ScalarConjugate.CM.SpectralConjugation

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.ScalarConjugate.CM.GaloisLift

/-! Extend automorphisms of a finite coefficient field to the actual
algebraic numbers and transport equality of coefficient tensors. -/

open scoped Classical TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ScalarConjugate.CM.Projectors

variable (K : IntermediateField ℚ ℂ) [NumberField K]

theorem le_algebraicField : K ≤ Coefficients.CM.algebraicField := by
  intro z hz
  apply mem_algebraicClosure_iff.mpr
  exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (⟨z, hz⟩ : K)).algHom K.val

/-- Normality extends the given automorphism, preserving its actual values
in the fixed complex coefficient field. -/
theorem exists_algebraic_lift (σ : Gal(K/ℚ)) :
    ∃ τ : Gal(Coefficients.CM.algebraicField/ℚ), ∀ a : K,
      (τ (IntermediateField.inclusion (le_algebraicField K) a) : ℂ) = (σ a : ℂ) := by
  let : Algebra K Coefficients.CM.algebraicField :=
    (IntermediateField.inclusion (le_algebraicField K)).toAlgebra
  let : IsScalarTower ℚ K Coefficients.CM.algebraicField := inferInstance
  let : IsAlgClosure ℚ Coefficients.CM.algebraicField := algebraicClosure.isAlgClosure ℚ ℂ
  exact ⟨σ.liftNormal Coefficients.CM.algebraicField, fun a =>
    congrArg (fun z : Coefficients.CM.algebraicField => (z : ℂ)) (σ.liftNormal_commutes Coefficients.CM.algebraicField a)⟩

variable {U : Type*} [AddCommGroup U] [Module ℚ U]

/-- Equality of the included tensors is retained after the matched scalar
automorphisms; no automorphism of the complex variety is involved. -/
theorem conjugate_inclusions_eq
    (p : K ⊗[ℚ] U) (q : Coefficients.CM.algebraicField ⊗[ℚ] U)
    (hpq : ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K U p = ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion Coefficients.CM.algebraicField U q)
    (σ : Gal(K/ℚ)) (τ : Gal(Coefficients.CM.algebraicField/ℚ))
    (hτ : ∀ a : K,
      (τ (IntermediateField.inclusion (le_algebraicField K) a) : ℂ) = (σ a : ℂ)) :
    ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K U (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K U σ p) =
      ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion Coefficients.CM.algebraicField U (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ Coefficients.CM.algebraicField U τ q) := by
  let incl : K ⊗[ℚ] U →ₗ[ℚ] Coefficients.CM.algebraicField ⊗[ℚ] U :=
    TensorProduct.map (IntermediateField.inclusion (le_algebraicField K)).toLinearMap
      LinearMap.id
  have hi : ∀ x : K ⊗[ℚ] U,
      ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion Coefficients.CM.algebraicField U (incl x) = ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K U x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a u => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have heq : incl p = q := Projectors.coefficientInclusion_injective Coefficients.CM.algebraicField
    ((hi p).trans hpq)
  rw [← heq]
  clear hpq heq
  induction p using TensorProduct.inductionOn with
  | tmul a u =>
      change ((σ a : K) : ℂ) ⊗ₜ[ℚ] u =
        (τ (IntermediateField.inclusion (le_algebraicField K) a) : ℂ) ⊗ₜ[ℚ] u
      rw [hτ]
  | add x y hx hy => simp only [map_add, hx, hy]

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.ScalarConjugate.CM.GaloisLift

end

end OAI
