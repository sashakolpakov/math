import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ModuleTraceHomology

/-! # Module Trace Bijective -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ModuleTraceBijective

noncomputable section

/-! The native top transfer is bijective exactly when the actual
module trace is bijective on the same target-cover cohomology. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left] [IsProper Y.hom] [Smooth Y.hom]
  {ι : Type u} (U : ι → Y.left.Opens) (g : ℕ) [SmoothOfRelativeDimension g Y.hom]

theorem iff : Function.Bijective (IntrinsicDeRham.TopEdgeTransfer.Intrinsic.trace R X Y f U g) ↔
    Function.Bijective (HomologicalComplex.homologyMap (ModuleCech.CohomologyNaturality.map R Y U
      (FiniteEtale.ModuleTrace.trace R X Y f g)) g) := by
  let e := (ModuleTraceHomology.pushforwardIso R X Y f U g g).addCommGroupIsoToAddEquiv
  let t := HomologicalComplex.homologyMap (ModuleCech.CohomologyNaturality.map R Y U
    (FiniteEtale.ModuleTrace.trace R X Y f g)) g
  have h : (IntrinsicDeRham.TopEdgeTransfer.Intrinsic.trace R X Y f U g : _ → _) = t ∘ e := by
    funext x
    have hx := ConcreteCategory.congr_hom (ModuleTraceHomology.comparison R X Y f U g g) x
    exact (ModuleTraceHomology.top_trace R X Y f U g x).symm.trans hx
  rw [h]
  constructor
  · intro hb
    have heq : (t : _ → _) = (t ∘ e) ∘ e.symm := by
      funext x
      exact congrArg t (e.apply_symm_apply x).symm
    rw [heq]
    exact hb.comp e.symm.bijective
  · intro hb
    exact hb.comp e.bijective

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ModuleTraceBijective
