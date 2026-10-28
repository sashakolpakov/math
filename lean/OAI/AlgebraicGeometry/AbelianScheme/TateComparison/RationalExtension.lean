import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AlbaneseRationalEnd
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Cohomology

/-! # Rational Extension -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Extending an additive actual integral H1 pullback gives precisely
the statement's all-denominator rational pullback relation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

def RationalExtension.rationalExtensionOfAddHom {M V : Type*} [AddCommGroup M] [AddCommGroup V] [Module ℚ V]
    (f : M →+ V) : ℚ ⊗[ℤ] M →ₗ[ℚ] V :=
  TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton ℚ (M →ₗ[ℤ] V) f.toIntLinearMap)

theorem RationalExtension.rationalExtensionOfAddHom_tmul {M V : Type*} [AddCommGroup M] [AddCommGroup V] [Module ℚ V]
    (f : M →+ V) (r : ℚ) (a : M) : RationalExtension.rationalExtensionOfAddHom f (r ⊗ₜ[ℤ] a) = r • f a := rfl

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)

theorem Data.SphericalPELAlbaneseData.pullbackH1Integral_zero : D.pullbackH1Integral 0 = 0 := by
  unfold Data.SphericalPELAlbaneseData.pullbackH1Integral
  rw [BaseChange.endSchemeMap_zero, Functor.map_one]
  exact PELModuli.IntegralModel.Product.bettiPullbackQ_one 1 (by decide)

def Data.SphericalPELAlbaneseData.integralH1PullbackAddHom
    (hadd : ∀ a b : D.EndK, D.pullbackH1Integral (a + b) = D.pullbackH1Integral a + D.pullbackH1Integral b) :
    D.EndK →+ Module.End ℚ D.H1 where
  toFun := D.pullbackH1Integral
  map_zero' := D.pullbackH1Integral_zero
  map_add' := hadd

def Data.SphericalPELAlbaneseData.rationalH1Pullback
    (hadd : ∀ a b : D.EndK, D.pullbackH1Integral (a + b) = D.pullbackH1Integral a + D.pullbackH1Integral b) :
    D.EndQ →ₗ[ℚ] Module.End ℚ D.H1 :=
  RationalExtension.rationalExtensionOfAddHom (D.integralH1PullbackAddHom hadd)

theorem Data.SphericalPELAlbaneseData.rationalH1Pullback_integral
    (hadd : ∀ a b : D.EndK, D.pullbackH1Integral (a + b) = D.pullbackH1Integral a + D.pullbackH1Integral b)
    (a : D.EndK) : D.rationalH1Pullback hadd (D.toRational a) = D.pullbackH1Integral a := by
  change RationalExtension.rationalExtensionOfAddHom (D.integralH1PullbackAddHom hadd) (1 ⊗ₜ[ℤ] a) = _
  rw [RationalExtension.rationalExtensionOfAddHom_tmul, one_smul]
  rfl

theorem Data.SphericalPELAlbaneseData.rationalH1Pullback_spec
    (hadd : ∀ a b : D.EndK, D.pullbackH1Integral (a + b) = D.pullbackH1Integral a + D.pullbackH1Integral b)
    (x : D.EndQ) : D.IsRationalH1Pullback x (D.rationalH1Pullback hadd x) := by
  obtain ⟨m, hm, a, ha⟩ := D.endQ_positive_denominator x
  refine ⟨⟨m, hm, a, ha⟩, ?_⟩
  intro n _ a ha
  have h := congrArg (D.rationalH1Pullback hadd) ha
  rw [map_nsmul, Data.SphericalPELAlbaneseData.rationalH1Pullback_integral] at h
  exact (Nat.cast_smul_eq_nsmul ℚ n _).trans h

theorem Data.SphericalPELAlbaneseData.isRationalH1Pullback_unique (x : D.EndQ) (f g : Module.End ℚ D.H1)
    (hf : D.IsRationalH1Pullback x f) (hg : D.IsRationalH1Pullback x g) : f = g := by
  obtain ⟨n, hn, a, ha⟩ := hf.1
  have he := (hf.2 n hn a ha).trans (hg.2 n hn a ha).symm
  exact (smul_right_injective (M := Module.End ℚ D.H1) (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))) he

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
