import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.FiniteLevelKernel
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CohomologyDifference
import OAI.NumberTheory.PadicHodge.IntegralComparison.SequentialKernelLimit

/-! # Finite Inverse Limit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.FiniteInverseLimit

noncomputable section

/-!
# IntegralComparison: original crystalline cohomology as the inverse limit of finite bounded cohomology

This is unconditional in degree zero. In positive degree it uses finiteness
of the actual bounded Ext groups in the preceding degree.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

private structure ModuleIsoChain (C : Type*) [Category C] where
  X₀ : C
  X₁ : C
  X₂ : C
  a : X₀ ≅ X₁
  b : X₁ ≅ X₂

private def ModuleIsoChain.compose {C : Type*} [Category C] (chain : ModuleIsoChain C) :
    chain.X₀ ≅ chain.X₂ := chain.a ≪≫ chain.b

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionComplexExact.sequence (p := p) (J := J) (δ := δ) f

-- Name the canonical additive and module structures once, so comparison types stay small.
local instance finiteSourceAdd (i : ℕ) :
    AddCommGroup (BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f i) :=
  inferInstance

local instance finiteSourceModule (i : ℕ) :
    Module R (BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f i) :=
  inferInstance

local instance finiteCompatibleAdd (i : ℕ) :
    AddCommGroup (CohomologyDifference.compatible (p := p) (J := J) (δ := δ) f i) :=
  inferInstance

local instance finiteCompatibleModule (i : ℕ) :
    Module R (CohomologyDifference.compatible (p := p) (J := J) (δ := δ) f i) :=
  inferInstance

local instance finiteKernelAdd (i : ℕ) :
    AddCommGroup (LinearMap.ker (CohomologyDifference.sequenceDifference
      (p := p) (J := J) (δ := δ) f i)) := inferInstance

local instance finiteKernelModule (i : ℕ) :
    Module R (LinearMap.ker (CohomologyDifference.sequenceDifference
      (p := p) (J := J) (δ := δ) f i)) := inferInstance

def diagram (i : ℕ) : ℕᵒᵖ ⥤ ModuleCat.{u + 2} R :=
  SequentialKernelLimit.diagram R
    (fun n => BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i)
    (fun n => CohomologyDifference.transition (p := p) (J := J) (δ := δ) f n i)

def kernelToCompatible (i : ℕ) :
    LinearMap.ker (CohomologyDifference.sequenceDifference (p := p) (J := J) (δ := δ) f i) ≃ₗ[R]
      CohomologyDifference.compatible (p := p) (J := J) (δ := δ) f i :=
  LinearEquiv.ofEq _ _ (congrArg LinearMap.ker (CohomologyDifference.middle_g_eq (p := p) (J := J) (δ := δ) f i))

def compatibleLimitIso (i : ℕ) :
    ModuleCat.of R (CohomologyDifference.compatible (p := p) (J := J) (δ := δ) f i) ≅
      limit (diagram (p := p) (J := J) (δ := δ) f i) :=
  SequentialKernelLimit.limitIso R
    (fun n => BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i)
    (fun n => CohomologyDifference.transition (p := p) (J := J) (δ := δ) f n i)

def sourceKernelLinearEquiv (i : ℕ) [Mono (HomologicalComplex.homologyMap (S).f i)] :
    BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f i ≃ₗ[R]
      LinearMap.ker (CohomologyDifference.sequenceDifference (p := p) (J := J) (δ := δ) f i) :=
  FiniteLevelKernel.kernelLinearEquiv (p := p) (J := J) (δ := δ) f i

def compatibleLinearEquiv (i : ℕ) [Mono (HomologicalComplex.homologyMap (S).f i)] :
    BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f i ≃ₗ[R]
      CohomologyDifference.compatible (p := p) (J := J) (δ := δ) f i :=
  (sourceKernelLinearEquiv (p := p) (J := J) (δ := δ) f i).trans
    (kernelToCompatible (p := p) (J := J) (δ := δ) f i)

private def comparisonChain (i : ℕ) [Mono (HomologicalComplex.homologyMap (S).f i)] :
    ModuleIsoChain (ModuleCat.{u + 2} R) where
  X₀ := _
  X₁ := _
  X₂ := _
  a := (compatibleLinearEquiv (p := p) (J := J) (δ := δ) f i).toModuleIso
  b := compatibleLimitIso (p := p) (J := J) (δ := δ) f i

def limitIso (i : ℕ) [Mono (HomologicalComplex.homologyMap (S).f i)] :=
  (ModuleIsoChain.compose (comparisonChain (p := p) (J := J) (δ := δ) f i))

def linearEquiv (i : ℕ) [Mono (HomologicalComplex.homologyMap (S).f i)] :
    BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f i ≃ₗ[R]
      (limit (diagram (p := p) (J := J) (δ := δ) f i) : ModuleCat.{u + 2} R) :=
  (limitIso (p := p) (J := J) (δ := δ) f i).toLinearEquiv

theorem linearEquiv_apply (i : ℕ) [Mono (HomologicalComplex.homologyMap (S).f i)]
    (x : BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f i) :
    linearEquiv (p := p) (J := J) (δ := δ) f i x =
      (compatibleLimitIso (p := p) (J := J) (δ := δ) f i).hom
        (compatibleLinearEquiv (p := p) (J := J) (δ := δ) f i x) := rfl

def linearEquiv_succ (i : ℕ)
    [∀ n, Finite (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i)] :
    BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f (i + 1) ≃ₗ[R]
      (limit (diagram (p := p) (J := J) (δ := δ) f (i + 1)) : ModuleCat.{u + 2} R) := by
  letI := FiniteLevelKernel.inclusion_mono_succ (p := p) (J := J) (δ := δ) f i
  exact linearEquiv (p := p) (J := J) (δ := δ) f (i + 1)

def linearEquiv_zero :
    BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f 0 ≃ₗ[R]
      (limit (diagram (p := p) (J := J) (δ := δ) f 0) : ModuleCat.{u + 2} R) := by
  letI := ShortExactHomologyKernel.mono_zero (S) (ResolutionComplexExact.shortExact f)
  exact linearEquiv (p := p) (J := J) (δ := δ) f 0

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.FiniteInverseLimit
