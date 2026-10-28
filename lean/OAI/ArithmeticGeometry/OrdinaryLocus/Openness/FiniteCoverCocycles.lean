import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PrincipalCoverFlat
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Finite Cover Cocycles -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteCoverCocycles.Construction

noncomputable section

/-! Explicit cocycle descent for a finite jointly faithfully flat family of algebras. -/

open scoped TensorProduct

universe u v w t

variable (R : Type u) [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (B : ι → Type w) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (M : Type t) [AddCommGroup M] [Module R M]

abbrev finiteCoverC0 := ∀ i, B i ⊗[R] M
abbrev finiteCoverC1 := ∀ i j, B i ⊗[R] (B j ⊗[R] M)
abbrev finiteCoverC2 := ∀ i j k, B i ⊗[R] (B j ⊗[R] (B k ⊗[R] M))

def finiteCoverD0 : finiteCoverC0 R B M →ₗ[R] finiteCoverC1 R B M :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    TensorProduct.mk R (B i) (B j ⊗[R] M) 1 ∘ₗ LinearMap.proj j -
      (TensorProduct.mk R (B j) M 1).lTensor (B i) ∘ₗ LinearMap.proj i

def finiteCoverD1 : finiteCoverC1 R B M →ₗ[R] finiteCoverC2 R B M :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦ LinearMap.pi fun k ↦
    TensorProduct.mk R (B i) (B j ⊗[R] (B k ⊗[R] M)) 1 ∘ₗ
        LinearMap.proj k ∘ₗ LinearMap.proj j -
      (TensorProduct.mk R (B j) (B k ⊗[R] M) 1).lTensor (B i) ∘ₗ
        LinearMap.proj k ∘ₗ LinearMap.proj i +
      ((TensorProduct.mk R (B k) M 1).lTensor (B j)).lTensor (B i) ∘ₗ
        LinearMap.proj j ∘ₗ LinearMap.proj i

def finiteCoverAmitsurEquiv0 : (∀ i, B i) ⊗[R] M ≃ₗ[R] finiteCoverC0 R B M :=
  TensorProduct.piLeft R M B

def finiteCoverAmitsurEquiv1 :
    (∀ i, B i) ⊗[R] ((∀ i, B i) ⊗[R] M) ≃ₗ[R] finiteCoverC1 R B M :=
  TensorProduct.piLeft R ((∀ i, B i) ⊗[R] M) B ≪≫ₗ
    LinearEquiv.piCongrRight fun i ↦
      (finiteCoverAmitsurEquiv0 R B M).lTensor (B i) ≪≫ₗ
        TensorProduct.piRight R R (B i) (fun j ↦ B j ⊗[R] M)

def finiteCoverAmitsurEquiv2 :
    (∀ i, B i) ⊗[R] ((∀ i, B i) ⊗[R] ((∀ i, B i) ⊗[R] M)) ≃ₗ[R]
      finiteCoverC2 R B M :=
  TensorProduct.piLeft R ((∀ i, B i) ⊗[R] ((∀ i, B i) ⊗[R] M)) B ≪≫ₗ
    LinearEquiv.piCongrRight fun i ↦
      (finiteCoverAmitsurEquiv1 R B M).lTensor (B i) ≪≫ₗ
        TensorProduct.piRight R R (B i) (fun j ↦ ∀ k, B j ⊗[R] (B k ⊗[R] M)) ≪≫ₗ
          LinearEquiv.piCongrRight fun j ↦
            TensorProduct.piRight R R (B i) (fun k ↦ B j ⊗[R] (B k ⊗[R] M))

theorem finiteCoverAmitsurEquiv0_tmul (b : ∀ i, B i) (m : M) (i : ι) :
    finiteCoverAmitsurEquiv0 R B M (b ⊗ₜ[R] m) i = b i ⊗ₜ[R] m := by
  simp [finiteCoverAmitsurEquiv0]

theorem finiteCoverAmitsurEquiv1_tmul (a b : ∀ i, B i) (m : M) (i j : ι) :
    finiteCoverAmitsurEquiv1 R B M (a ⊗ₜ[R] (b ⊗ₜ[R] m)) i j =
      a i ⊗ₜ[R] (b j ⊗ₜ[R] m) := by
  simp [finiteCoverAmitsurEquiv1, finiteCoverAmitsurEquiv0]

theorem finiteCoverAmitsurEquiv2_tmul (a b c : ∀ i, B i) (m : M) (i j k : ι) :
    finiteCoverAmitsurEquiv2 R B M (a ⊗ₜ[R] (b ⊗ₜ[R] (c ⊗ₜ[R] m))) i j k =
      a i ⊗ₜ[R] (b j ⊗ₜ[R] (c k ⊗ₜ[R] m)) := by
  simp [finiteCoverAmitsurEquiv2, finiteCoverAmitsurEquiv1, finiteCoverAmitsurEquiv0]

theorem finiteCoverD0_comparison :
    finiteCoverD0 R B M ∘ₗ (finiteCoverAmitsurEquiv0 R B M).toLinearMap =
      (finiteCoverAmitsurEquiv1 R B M).toLinearMap ∘ₗ AmitsurDegreeOne.Construction.amitsurD0 R (∀ i, B i) M := by
  ext b m i j
  simp [finiteCoverD0, AmitsurDegreeOne.Construction.amitsurD0_tmul, finiteCoverAmitsurEquiv0_tmul,
    finiteCoverAmitsurEquiv1_tmul]

theorem finiteCoverD1_comparison :
    finiteCoverD1 R B M ∘ₗ (finiteCoverAmitsurEquiv1 R B M).toLinearMap =
      (finiteCoverAmitsurEquiv2 R B M).toLinearMap ∘ₗ AmitsurDegreeOne.Construction.amitsurD1 R (∀ i, B i) M := by
  ext a b m i j k
  simp [finiteCoverD1, AmitsurDegreeOne.Construction.amitsurD1_tmul, finiteCoverAmitsurEquiv1_tmul,
    finiteCoverAmitsurEquiv2_tmul]

theorem finiteCoverD0_comparison_apply (x : (∀ i, B i) ⊗[R] M) :
    finiteCoverD0 R B M (finiteCoverAmitsurEquiv0 R B M x) =
      finiteCoverAmitsurEquiv1 R B M (AmitsurDegreeOne.Construction.amitsurD0 R (∀ i, B i) M x) :=
  LinearMap.congr_fun (finiteCoverD0_comparison R B M) x

theorem finiteCoverD1_comparison_apply (x : (∀ i, B i) ⊗[R] ((∀ i, B i) ⊗[R] M)) :
    finiteCoverD1 R B M (finiteCoverAmitsurEquiv1 R B M x) =
      finiteCoverAmitsurEquiv2 R B M (AmitsurDegreeOne.Construction.amitsurD1 R (∀ i, B i) M x) :=
  LinearMap.congr_fun (finiteCoverD1_comparison R B M) x

theorem finiteCoverD1_comp_D0 : finiteCoverD1 R B M ∘ₗ finiteCoverD0 R B M = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := (finiteCoverAmitsurEquiv0 R B M).surjective x
  change finiteCoverD1 R B M (finiteCoverD0 R B M (finiteCoverAmitsurEquiv0 R B M y)) = 0
  rw [finiteCoverD0_comparison_apply, finiteCoverD1_comparison_apply]
  have h := LinearMap.congr_fun (AmitsurDegreeOne.Construction.amitsurD1_comp_D0 R (∀ i, B i) M) y
  change AmitsurDegreeOne.Construction.amitsurD1 R (∀ i, B i) M (AmitsurDegreeOne.Construction.amitsurD0 R (∀ i, B i) M y) = 0 at h
  rw [h, map_zero]

theorem finiteCover_exact_degreeOne [Module.FaithfullyFlat R (∀ i, B i)] :
    Function.Exact (finiteCoverD0 R B M) (finiteCoverD1 R B M) := by
  intro z
  constructor
  · intro hz
    obtain ⟨w, rfl⟩ := (finiteCoverAmitsurEquiv1 R B M).surjective z
    rw [finiteCoverD1_comparison_apply] at hz
    have hw : AmitsurDegreeOne.Construction.amitsurD1 R (∀ i, B i) M w = 0 :=
      (finiteCoverAmitsurEquiv2 R B M).injective (hz.trans (map_zero _).symm)
    obtain ⟨x, hx⟩ := (AmitsurDegreeOne.Construction.amitsur_exact_degreeOne R (∀ i, B i) M w).mp hw
    refine ⟨finiteCoverAmitsurEquiv0 R B M x, ?_⟩
    rw [finiteCoverD0_comparison_apply, hx]
  · rintro ⟨x, rfl⟩
    exact LinearMap.congr_fun (finiteCoverD1_comp_D0 R B M) x

def finiteCoverUnit : M →ₗ[R] finiteCoverC0 R B M :=
  LinearMap.pi fun i ↦ TensorProduct.mk R (B i) M 1

theorem finiteCoverUnit_comparison (m : M) :
    finiteCoverUnit R B M m = finiteCoverAmitsurEquiv0 R B M (1 ⊗ₜ[R] m) := by
  ext i
  simp [finiteCoverUnit, finiteCoverAmitsurEquiv0_tmul]

theorem finiteCover_exact_degreeZero [Module.FaithfullyFlat R (∀ i, B i)] :
    Function.Exact (finiteCoverUnit R B M) (finiteCoverD0 R B M) := by
  intro z
  constructor
  · intro hz
    obtain ⟨w, rfl⟩ := (finiteCoverAmitsurEquiv0 R B M).surjective z
    rw [finiteCoverD0_comparison_apply] at hz
    have hw : AmitsurDegreeOne.Construction.amitsurD0 R (∀ i, B i) M w = 0 :=
      (finiteCoverAmitsurEquiv1 R B M).injective (hz.trans (map_zero _).symm)
    obtain ⟨m, hm⟩ := (AmitsurDegreeOne.Construction.amitsur_exact_degreeZero R (∀ i, B i) M w).mp hw
    refine ⟨m, ?_⟩
    rw [finiteCoverUnit_comparison]
    exact congrArg (finiteCoverAmitsurEquiv0 R B M) hm
  · rintro ⟨m, rfl⟩
    rw [finiteCoverUnit_comparison, finiteCoverD0_comparison_apply]
    simp [AmitsurDegreeOne.Construction.amitsurD0_tmul]

theorem finiteCoverUnit_injective [Module.FaithfullyFlat R (∀ i, B i)] :
    Function.Injective (finiteCoverUnit R B M) := by
  intro x y h
  rw [finiteCoverUnit_comparison, finiteCoverUnit_comparison] at h
  exact AmitsurDegreeOne.Construction.amitsur_unit_injective R (∀ i, B i) M
    ((finiteCoverAmitsurEquiv0 R B M).injective h)

theorem principalCover_cocycle_is_coboundary (f : ι → R)
    (hf : Ideal.span (Set.range f) = ⊤)
    (z : finiteCoverC1 R (fun i ↦ Localization.Away (f i)) M)
    (hz : finiteCoverD1 R (fun i ↦ Localization.Away (f i)) M z = 0) :
    ∃ x, finiteCoverD0 R (fun i ↦ Localization.Away (f i)) M x = z := by
  let := PrincipalCoverFlat.Construction.faithfullyFlat_principalCover R f hf
  exact (finiteCover_exact_degreeOne R (fun i ↦ Localization.Away (f i)) M z).mp hz

theorem principalCover_sections_glue (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (x : finiteCoverC0 R (fun i ↦ Localization.Away (f i)) M)
    (hx : finiteCoverD0 R (fun i ↦ Localization.Away (f i)) M x = 0) :
    ∃! m, finiteCoverUnit R (fun i ↦ Localization.Away (f i)) M m = x := by
  let := PrincipalCoverFlat.Construction.faithfullyFlat_principalCover R f hf
  obtain ⟨m, hm⟩ :=
    (finiteCover_exact_degreeZero R (fun i ↦ Localization.Away (f i)) M x).mp hx
  refine ⟨m, hm, fun n hn ↦ ?_⟩
  exact finiteCoverUnit_injective R (fun i ↦ Localization.Away (f i)) M (hn.trans hm.symm)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteCoverCocycles.Construction
