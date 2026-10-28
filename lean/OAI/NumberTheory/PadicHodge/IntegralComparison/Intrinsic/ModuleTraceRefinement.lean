import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.BaseChangeRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ModuleTraceHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.RefinedTransferTrace

/-! # Module Trace Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ModuleTraceRefinement

noncomputable section

/-! Native finite étale top-form transfer is compatible with
the canonical cohomology comparison for a refinement of covers. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left] [IsProper Y.hom] [Smooth Y.hom]
  {ι κ : Type u} (U : ι → Y.left.Opens) (V : κ → Y.left.Opens)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U) (g : ℕ)
local notation "F" => Opens.map f.left.base
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CohomologyNaturality.forgetCoefficients R
local notation "W₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechTransfer.Intrinsic.inverseCover R X Y f U
local notation "W₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechTransfer.Intrinsic.inverseCover R X Y f V
local notation "M" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g
local notation "N" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y g
local instance opens_finiteLimits : PreservesFiniteLimits (Opens.map f.left.base) := by
  change PreservesFiniteLimits (OrderHom.ofClass f.left.base.frameHom).toFunctor
  infer_instance

theorem complex :
    ModuleCechTrace.trace R X Y f U g ≫ ModuleCech.CoverRefinement.map R Y U V r N =
      ModuleCech.CoverRefinement.map R X W₁ W₂
        (Cech.BaseChangeRefinement.refinement (F) U V r) M ≫
          ModuleCechTrace.trace R X Y f V g := by
  rw [ModuleCechTrace.trace_eq, ModuleCechTrace.trace_eq]
  exact Cech.BaseChangeRefinement.transfer (F) U V r
    (ModuleTracePresheaf.transfer R X Y f g)

variable [X.left.IsSeparated] [Y.left.IsSeparated]
  [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]
  [SmoothOfRelativeDimension g Y.hom]
  (hU : ⨆ i, U i = ⊤) (hV : ⨆ i, V i = ⊤)
  (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ i, IsAffineOpen (V i))
  (hg : 0 < g)
local instance source_qc : (M).IsQuasicoherent := by
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  exact IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent R X g
local instance target_qc : (N).IsQuasicoherent := IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent R Y g

include r in
omit [SmoothOfRelativeDimension g Y.hom] in
theorem cohomology :
    (G).map (HomologicalComplex.homologyMap (ModuleCechTrace.trace R X Y f U g) g) ≫
        (ModuleCech.PositiveCover.Comparison.iso R Y U V hU hV haU haV N g hg).hom =
      (ModuleCech.PositiveCover.Comparison.iso R X W₁ W₂
        (RefinedTransferTrace.inverseCover_top R X Y f U hU)
        (RefinedTransferTrace.inverseCover_top R X Y f V hV)
        (RefinedTransferTrace.inverseCover_affine R X Y f U haU)
        (RefinedTransferTrace.inverseCover_affine R X Y f V haV) M g hg).hom ≫
          (G).map (HomologicalComplex.homologyMap (ModuleCechTrace.trace R X Y f V g) g) := by
  have h := congrArg (fun z => (G).map (HomologicalComplex.homologyMap z g))
    (complex R X Y f U V r g)
  simp only [HomologicalComplex.homologyMap_comp, Functor.map_comp] at h
  rw [ModuleCech.TraceRefinement.map_eq_positiveCoverIso R Y U V r hU hV haU haV N g hg,
    ModuleCech.TraceRefinement.map_eq_positiveCoverIso R X W₁ W₂
      (Cech.BaseChangeRefinement.refinement (F) U V r)
      (RefinedTransferTrace.inverseCover_top R X Y f U hU)
      (RefinedTransferTrace.inverseCover_top R X Y f V hV)
      (RefinedTransferTrace.inverseCover_affine R X Y f U haU)
      (RefinedTransferTrace.inverseCover_affine R X Y f V haV) M g hg] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ModuleTraceRefinement
