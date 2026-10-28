import OAI.Analysis.Normed.Function.Holder.Banach.Maps
import OAI.Analysis.Normed.Function.Holder.DerivativeBanach

open Set Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance firstDerivativeNormedGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance firstDerivativeNormedSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance secondDerivativeNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance
local instance secondDerivativeNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance

abbrev SecondJetAmbient (K : Set E) (α : ℝ) :=
  (K →ᵇ F) × (K →ᵇ (E →L[ℝ] F)) × HolderMap K (E →L[ℝ] E →L[ℝ] F) α

def valueGradientMap (K : Set E) (α : ℝ) :
    SecondJetAmbient (F := F) K α →L[ℝ] ((K →ᵇ F) × (K →ᵇ (E →L[ℝ] F))) where
  toFun p := (p.1, p.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_fst.prodMk continuous_snd.fst

def gradientHessianMap (K : Set E) (α : ℝ) :
    SecondJetAmbient (F := F) K α →L[ℝ]
      ((K →ᵇ (E →L[ℝ] F)) × (K →ᵇ (E →L[ℝ] E →L[ℝ] F))) where
  toFun p := (p.2.1, OAI.Analysis.Normed.Function.Holder.HolderMap.value p.2.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_snd.fst.prodMk (OAI.Analysis.Normed.Function.Holder.HolderMap.valueCLM.continuous.comp continuous_snd.snd)

/-- The two derivative-compatibility conditions define a closed linear
subspace of the value/gradient/Hölder-Hessian product. -/
def secondJetGraph {Ω K : Set E} (hΩK : Ω ⊆ K) (α : ℝ) :
    Submodule ℝ (SecondJetAmbient (F := F) K α) :=
  (derivativeGraph (F := F) hΩK).comap (valueGradientMap K α).toLinearMap ⊓
  (derivativeGraph (F := E →L[ℝ] F) hΩK).comap (gradientHessianMap K α).toLinearMap

abbrev C2Holder {Ω K : Set E} (hΩK : Ω ⊆ K) (α : ℝ) : Type _ :=
  ↥(secondJetGraph (F := F) hΩK α)

instance instC2HolderNormedAddCommGroup {Ω K : Set E} (hΩK : Ω ⊆ K) (α : ℝ) :
    NormedAddCommGroup (C2Holder (F := F) hΩK α) := inferInstance

instance instC2HolderNormedSpace {Ω K : Set E} (hΩK : Ω ⊆ K) (α : ℝ) :
    NormedSpace ℝ (C2Holder (F := F) hΩK α) := inferInstance

theorem isClosed_secondJetGraph {Ω K : Set E} (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K) (α : ℝ) :
    IsClosed (secondJetGraph (F := F) hΩK α : Set (SecondJetAmbient (F := F) K α)) := by
  exact ((isClosed_derivativeGraph (F := F) hΩ hΩK).preimage
    (valueGradientMap K α).continuous).inter
    ((isClosed_derivativeGraph (F := E →L[ℝ] F) hΩ hΩK).preimage
      (gradientHessianMap K α).continuous)

instance {Ω K : Set E} [Fact (IsOpen Ω)] (hΩK : Ω ⊆ K) (α : ℝ) [CompleteSpace F] :
    CompleteSpace (C2Holder (F := F) hΩK α) := by
  let : CompleteSpace (E →L[ℝ] F) := inferInstance
  let : CompleteSpace (E →L[ℝ] E →L[ℝ] F) := inferInstance
  let : CompleteSpace (K →ᵇ F) := inferInstance
  let : CompleteSpace (K →ᵇ (E →L[ℝ] F)) := inferInstance
  let : CompleteSpace (HolderMap K (E →L[ℝ] E →L[ℝ] F) α) := inferInstance
  let : CompleteSpace ((K →ᵇ (E →L[ℝ] F)) ×
      HolderMap K (E →L[ℝ] E →L[ℝ] F) α) := inferInstance
  let : CompleteSpace (SecondJetAmbient (F := F) K α) := inferInstance
  exact (isClosed_secondJetGraph (F := F) Fact.out hΩK α).isComplete.completeSpace_coe

namespace C2Holder

variable {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}

def value (f : C2Holder (F := F) hΩK α) : K →ᵇ F := f.val.1
def firstDerivative (f : C2Holder (F := F) hΩK α) : K →ᵇ (E →L[ℝ] F) := f.val.2.1
def secondDerivative (f : C2Holder (F := F) hΩK α) : K →ᵇ (E →L[ℝ] E →L[ℝ] F) :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val.2.2

theorem hasFDerivAt_value (f : C2Holder (F := F) hΩK α) {x : E} (hx : x ∈ Ω) :
    HasFDerivAt (boundedZeroExtension (C2Holder.value f)) (C2Holder.firstDerivative f ⟨x, hΩK hx⟩) x :=
  f.property.1 x hx

theorem hasFDerivAt_firstDerivative (f : C2Holder (F := F) hΩK α) {x : E} (hx : x ∈ Ω) :
    HasFDerivAt (boundedZeroExtension (C2Holder.firstDerivative f))
      (C2Holder.secondDerivative f ⟨x, hΩK hx⟩) x := f.property.2 x hx

theorem norm_value_le (f : C2Holder (F := F) hΩK α) : ‖C2Holder.value f‖ ≤ ‖f‖ := le_max_left _ _

theorem norm_firstDerivative_le (f : C2Holder (F := F) hΩK α) :
    ‖C2Holder.firstDerivative f‖ ≤ ‖f‖ := (le_max_left _ _).trans (le_max_right _ _)

theorem secondDerivative_holder (f : C2Holder (F := F) hΩK α) (x y : K) :
    ‖C2Holder.secondDerivative f x - C2Holder.secondDerivative f y‖ ≤ ‖f‖ * (dist x y) ^ α := by
  have hh := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le f.val.2.2 x y
  exact hh.trans (mul_le_mul_of_nonneg_right
    ((le_max_right _ _).trans (le_max_right _ _)) (Real.rpow_nonneg dist_nonneg _))

end C2Holder
end OAI.Analysis.Normed.Function.Holder
