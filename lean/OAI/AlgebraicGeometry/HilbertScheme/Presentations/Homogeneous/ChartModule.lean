import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.RingLocalization
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.DegreePieces
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.LocalizationFlat

/-! # Chart Module -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.ChartModule.GradedModules

noncomputable section

/-! The degree-zero module of a localized graded algebra is its actual homogeneous chart ring. -/

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.LocalizationFlat.GradedHilbert

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {B : Type w} [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule R B) [SetLike.GradedSMul 𝒜 ℳ]
variable (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ]

def homogeneousChartVal (b : B) :
    HomogeneousLocalization.Away ℬ b →ₗ[R] Localization.Away b where
  toFun := HomogeneousLocalization.val
  map_add' := HomogeneousLocalization.val_add
  map_smul' := HomogeneousLocalization.val_smul _

theorem homogeneousChartVal_injective (b : B) :
    Function.Injective (homogeneousChartVal (R := R) ℬ b) :=
  HomogeneousLocalization.val_injective _

variable (hnat : ∀ d : ℕ, ℳ (d : ℤ) = ℬ d)
variable (a : A) (e : ℕ) (ha : a ∈ 𝒜 (e : ℤ))
variable (hb : algebraMap A B a ∈ ℬ e)

include hnat hb in
theorem homogeneousChartVal_mem_degree (x : HomogeneousLocalization.Away ℬ (algebraMap A B a)) :
    (Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv (R := R) B a).symm (homogeneousChartVal ℬ _ x) ∈
      Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ a (e : ℤ) 0 := by
  obtain ⟨k, b, hbk, rfl⟩ := HomogeneousLocalization.Away.mk_surjective ℬ hb x
  have hm : b ∈ ℳ (0 + (k : ℤ) * (e : ℤ)) := by
    simpa only [zero_add, ← Nat.cast_mul, hnat, smul_eq_mul] using hbk
  have heq := Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv_fraction (R := R) B a k b
  have heq' : (Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv (R := R) B a).symm
      (homogeneousChartVal ℬ _ (HomogeneousLocalization.Away.mk ℬ hb k b hbk)) =
      Module.Fractions.GradedModules.moduleFractionMap (R := R) a k b := by
    apply (Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv (R := R) B a).injective
    rw [LinearEquiv.apply_symm_apply, heq]
    rfl
  rw [heq']
  exact Localized.DegreePieces.GradedModules.moduleFractionMap_mem_degree ℳ a (e : ℤ) 0 k b hm

def homogeneousChartToModuleZero :
    HomogeneousLocalization.Away ℬ (algebraMap A B a) →ₗ[R]
      Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ a (e : ℤ) 0 :=
  ((Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv (R := R) B a).symm.toLinearMap.comp
    (homogeneousChartVal ℬ _)).codRestrict _
      (homogeneousChartVal_mem_degree ℳ ℬ hnat a e hb)

include ha in
theorem homogeneousChartToModuleZero_bijective :
    Function.Bijective (homogeneousChartToModuleZero ℳ ℬ hnat a e hb) := by
  constructor
  · intro x y hxy
    apply homogeneousChartVal_injective ℬ (algebraMap A B a)
    apply (Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv (R := R) B a).symm.injective
    exact congrArg Subtype.val hxy
  · intro x
    obtain ⟨k, b, hbk, hbx⟩ :=
      (Localized.DegreePieces.GradedModules.mem_localizedDegreePiece_iff 𝒜 ℳ a (e : ℤ) ha 0 x.val).mp x.property
    have hm : b ∈ ℬ (k • e) := by
      simpa only [zero_add, ← Nat.cast_mul, hnat, smul_eq_mul] using hbk
    refine ⟨HomogeneousLocalization.Away.mk ℬ hb k b hm, ?_⟩
    apply Subtype.ext
    apply (Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv (R := R) B a).injective
    change (Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv (R := R) B a)
      ((Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv (R := R) B a).symm _) = _
    rw [LinearEquiv.apply_symm_apply, ← hbx, Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv_fraction]
    rfl

def homogeneousChartModuleEquiv :
    HomogeneousLocalization.Away ℬ (algebraMap A B a) ≃ₗ[R]
      Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ a (e : ℤ) 0 :=
  LinearEquiv.ofBijective (homogeneousChartToModuleZero ℳ ℬ hnat a e hb)
    (homogeneousChartToModuleZero_bijective 𝒜 ℳ ℬ hnat a e ha hb)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.ChartModule.GradedModules
