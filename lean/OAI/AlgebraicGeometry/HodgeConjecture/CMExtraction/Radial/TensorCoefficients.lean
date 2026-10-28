import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.TensorSpan
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Hecke
import OAI.RepresentationTheory.Hecke.RadialDilation.TensorCommutant

/-! # Tensor Coefficients -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.TensorCoefficients

noncomputable section

/-! Unique finite ball expansions of radial product tests. Their auxiliary
coefficients are concrete differences of two spherical slices, so every
away operator fixing the product also fixes each coefficient. -/

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm OAI.RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization

variable (q : ℕ) [Fact q.Prime]
  {Y : Type*} [TopologicalSpace Y] [T2Space Y]

def radialTestLinear : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q) where
  toFun := RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization.radialTest q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def radialTensorSum : (ℤ →₀ RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace Y) →ₗ[ℂ] RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q × Y) :=
  Finsupp.lsum ℂ (fun n : ℤ => RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorLeftLinear (RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization.radialTest q (Cyclicity.ball q n)))

theorem radialTensorSum_single (n : ℤ) (φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace Y) :
    radialTensorSum q (Finsupp.single n φ) = RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest (RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization.radialTest q (Cyclicity.ball q n)) φ :=
  Finsupp.lsum_single _ _ _ _

def radialAuxiliaryCoefficient (n : ℤ) : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q × Y) →ₗ[ℂ] RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace Y :=
  RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.testRightSection (Hecke.spherePoint q n) - RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.testRightSection (Hecke.spherePoint q (n - 1))

theorem radialAuxiliaryCoefficient_tensor (n : ℤ) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) (φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace Y) :
    radialAuxiliaryCoefficient q n (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest (RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization.radialTest q b) φ) = Hecke.shellCoefficient q n b • φ := by
  change RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.testRightSection (Hecke.spherePoint q n) (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest (RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization.radialTest q b) φ) -
    RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.testRightSection (Hecke.spherePoint q (n - 1)) (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest (RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization.radialTest q b) φ) = _
  rw [RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.testRightSection_tensor, RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.testRightSection_tensor]
  exact (sub_smul (b.val (Hecke.spherePoint q n)) (b.val (Hecke.spherePoint q (n - 1))) φ).symm

theorem radialAuxiliaryCoefficient_sum (n : ℤ) (a : ℤ →₀ RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace Y) :
    radialAuxiliaryCoefficient q n (radialTensorSum q a) = a n := by
  induction a using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  | add a b ha hb => simp only [map_add, ha, hb, Finsupp.coe_add, Pi.add_apply]
  | single m φ =>
      rw [radialTensorSum_single, radialAuxiliaryCoefficient_tensor, Hecke.shellCoefficient_ball]
      by_cases h : n = m
      · subst m; simp
      · simp [h]

theorem radialTensorSum_injective : Function.Injective (radialTensorSum q (Y := Y)) := by
  intro a b h
  apply Finsupp.ext
  intro n
  simpa only [radialAuxiliaryCoefficient_sum] using congrArg (radialAuxiliaryCoefficient q n) h

theorem radialTensorSum_range :
    LinearMap.range (radialTensorSum q (Y := Y)) =
      Submodule.span ℂ {F | ∃ (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) (φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace Y),
        F = RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest (RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization.radialTest q b) φ} := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    induction a using Finsupp.induction_linear with
    | zero => simpa only [map_zero] using (Submodule.zero_mem _)
    | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
    | single n φ => rw [radialTensorSum_single]; exact Submodule.subset_span ⟨Cyclicity.ball q n, φ, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨b, φ, rfl⟩
    let T := (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorRightLinear φ).comp (radialTestLinear q)
    have h : (⊤ : Submodule ℂ (RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q)) ≤ (LinearMap.range (radialTensorSum q)).comap T := by
      rw [← Hecke.radial_ball_span q]
      apply Submodule.span_le.mpr
      rintro _ ⟨n, rfl⟩
      exact ⟨Finsupp.single n φ, radialTensorSum_single q n φ⟩
    exact h Submodule.mem_top

theorem radialAuxiliaryCoefficient_right (n : ℤ)
    (V : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace Y ≃ₗ[ℂ] RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace Y) (F : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q × Y)) :
    radialAuxiliaryCoefficient q n (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.rightTestHom V F) = V (radialAuxiliaryCoefficient q n F) := by
  have h : (radialAuxiliaryCoefficient q n).comp (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.rightTestHom V).toLinearMap =
      V.toLinearMap.comp (radialAuxiliaryCoefficient q n) := by
    apply RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.test_linear_ext
    intro f φ
    change radialAuxiliaryCoefficient q n (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.rightTestHom V (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest f φ)) =
      V (radialAuxiliaryCoefficient q n (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest f φ))
    rw [RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.rightTestHom_tensor]
    change RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.testRightSection (Hecke.spherePoint q n) (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest f (V φ)) -
      RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.testRightSection (Hecke.spherePoint q (n - 1)) (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest f (V φ)) =
      V (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.testRightSection (Hecke.spherePoint q n) (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest f φ) -
        RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.testRightSection (Hecke.spherePoint q (n - 1)) (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest f φ))
    simp only [RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.testRightSection_tensor, map_sub, map_smul]
  exact LinearMap.congr_fun h F

theorem radialTensorSum_fixed_coefficients (a : ℤ →₀ RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace Y)
    (V : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace Y ≃ₗ[ℂ] RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace Y)
    (h : RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.rightTestHom V (radialTensorSum q a) = radialTensorSum q a) (n : ℤ) : V (a n) = a n := by
  have he := congrArg (radialAuxiliaryCoefficient q n) h
  rwa [radialAuxiliaryCoefficient_right, radialAuxiliaryCoefficient_sum] at he

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.TensorCoefficients
