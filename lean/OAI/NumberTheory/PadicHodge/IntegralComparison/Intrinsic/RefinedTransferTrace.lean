import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TopFormPullbackRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TopFormTransferDegree
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.TraceRefinement

/-! # Refined Transfer Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.RefinedTransferTrace

noncomputable section

/-! Transport of a genuine target trace and a bijective native
transfer to a refined source cover, retaining the actual rank formula. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left]
  {ι κ : Type u} (U : ι → Y.left.Opens) (V : κ → X.left.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ f.left ⁻¹ᵁ U (r i))
  (hU : ⨆ i, U i = ⊤) (hV : ⨆ i, V i = ⊤)
  (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ i, IsAffineOpen (V i))
  (g : ℕ) [SmoothOfRelativeDimension g X.hom] [IsProper X.hom] [X.left.IsSeparated]
  [SmoothOfRelativeDimension g Y.hom] [IsProper Y.hom]
  (hg : 0 < g)
local notation "W" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechTransfer.Intrinsic.inverseCover R X Y f U
local notation "M" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g
local instance source_form_qc : (M).IsQuasicoherent := by
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  exact IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent R X g

include hU in
omit [IsFinite f.left] [Etale f.left] [IsProper X.hom] [X.left.IsSeparated] [IsProper Y.hom] in
theorem inverseCover_top : (⨆ i, W i) = ⊤ := by
  apply top_unique
  intro x _
  have hx : f.left x ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

include haU in
omit [Etale f.left] [IsProper X.hom] [X.left.IsSeparated] [IsProper Y.hom] in
theorem inverseCover_affine (i : ι) : IsAffineOpen (W i) := (haU i).preimage f.left

def coverIso : AddCommGrpCat.of (IntrinsicDeRham.TopEdge.Intrinsic.source R X W g) ≅
    AddCommGrpCat.of (IntrinsicDeRham.TopEdge.Intrinsic.source R X V g) :=
  ModuleCech.PositiveCover.Comparison.iso R X W V
    (inverseCover_top R X Y f U hU) hV (inverseCover_affine R X Y f U haU) haV M g hg

variable {C : Type v} [AddCommGroup C]
  (t : IntrinsicDeRham.TopEdge.Intrinsic.source R Y U g ≃+ C)
  (hb : Function.Bijective (IntrinsicDeRham.TopEdgeTransfer.Intrinsic.trace R X Y f U g))

def inverseTrace : IntrinsicDeRham.TopEdge.Intrinsic.source R X W g ≃+ C :=
  (AddEquiv.ofBijective (IntrinsicDeRham.TopEdgeTransfer.Intrinsic.trace R X Y f U g).toAddMonoidHom hb).trans t

def trace : IntrinsicDeRham.TopEdge.Intrinsic.source R X V g ≃+ C :=
  (coverIso R X Y f U V hU hV haU haV g hg).symm.addCommGroupIsoToAddEquiv.trans
    (inverseTrace R X Y f U g t hb)

variable [PreconnectedSpace Y.left]

theorem pullback (y : Y.left) (x : IntrinsicDeRham.TopEdge.Intrinsic.source R Y U g) :
    trace R X Y f U V hU hV haU haV g hg t hb
      (IntrinsicDeRham.TopEdgeMap.Intrinsic.rowMap R X Y V U g
        (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechCoordinatePullback.BaseIntrinsicCechCoordinatePullback.sheafMap R f U V r hr) x) =
      f.left.finrank y • t x := by
  rw [TopFormPullbackRefinement.pullback]
  have h := ModuleCech.TraceRefinement.refinement R X W V
    (TopFormPullbackRefinement.refinement R X Y f U V r hr)
    (inverseCover_top R X Y f U hU) hV (inverseCover_affine R X Y f U haU) haV M g hg
    (inverseTrace R X Y f U g t hb).toAddMonoidHom
    (IntrinsicDeRham.TopEdgeTransfer.Intrinsic.pullback R X Y f U g x)
  change _ = t (IntrinsicDeRham.TopEdgeTransfer.Intrinsic.trace R X Y f U g
    (IntrinsicDeRham.TopEdgeTransfer.Intrinsic.pullback R X Y f U g x)) at h
  exact h.trans ((congrArg t (TopFormTransferDegree.pullback_trace R X Y f U g y x)).trans
    (map_nsmul t (f.left.finrank y) x))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.RefinedTransferTrace
