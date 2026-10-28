import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ModuleTraceRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PositiveTransitivity

/-! # Module Trace Cover Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ModuleTraceCoverNaturality

noncomputable section

/-! The original top-form transfer respects arbitrary affine-cover
comparisons, via the common intersection refinement. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem square {C : Type*} [Category C] {A₁ A₂ A₃ B₁ B₂ B₃ : C}
    (s₁₂ : A₁ ⟶ A₂) (s₂₃ : A₂ ⟶ A₃) (s₁₃ : A₁ ⟶ A₃)
    (t₁₂ : B₁ ⟶ B₂) (t₂₃ : B₂ ⟶ B₃) (t₁₃ : B₁ ⟶ B₃) [Mono t₂₃]
    (a₁ : A₁ ⟶ B₁) (a₂ : A₂ ⟶ B₂) (a₃ : A₃ ⟶ B₃)
    (hs : s₁₂ ≫ s₂₃ = s₁₃) (ht : t₁₂ ≫ t₂₃ = t₁₃)
    (h₁ : a₁ ≫ t₁₃ = s₁₃ ≫ a₃) (h₂ : a₂ ≫ t₂₃ = s₂₃ ≫ a₃) :
    a₁ ≫ t₁₂ = s₁₂ ≫ a₂ := by
  apply (cancel_mono t₂₃).mp
  rw [Category.assoc, ht, h₁, ← hs, Category.assoc, ← h₂, ← Category.assoc]

universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left] [IsProper Y.hom] [Smooth Y.hom]
  [X.left.IsSeparated] [Y.left.IsSeparated]
  {ι κ : Type u} (U : ι → Y.left.Opens) (V : κ → Y.left.Opens)
  (g : ℕ) [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]
  [SmoothOfRelativeDimension g Y.hom]
  (hU : ⨆ i, U i = ⊤) (hV : ⨆ i, V i = ⊤)
  (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ i, IsAffineOpen (V i))
  (hg : 0 < g)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CohomologyNaturality.forgetCoefficients R
local notation "W₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechTransfer.Intrinsic.inverseCover R X Y f U
local notation "W₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechTransfer.Intrinsic.inverseCover R X Y f V
local notation "M" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g
local notation "N" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y g
local instance source_qc : (M).IsQuasicoherent := by
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  exact IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent R X g
local instance target_qc : (N).IsQuasicoherent := IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent R Y g

def sourceIso := ModuleCech.PositiveCover.Comparison.iso R X W₁ W₂
  (RefinedTransferTrace.inverseCover_top R X Y f U hU)
  (RefinedTransferTrace.inverseCover_top R X Y f V hV)
  (RefinedTransferTrace.inverseCover_affine R X Y f U haU)
  (RefinedTransferTrace.inverseCover_affine R X Y f V haV) M g hg

omit [SmoothOfRelativeDimension g Y.hom] in
theorem cohomology :
    (G).map (HomologicalComplex.homologyMap (ModuleCechTrace.trace R X Y f U g) g) ≫
        (ModuleCech.PositiveCover.Comparison.iso R Y U V hU hV haU haV N g hg).hom =
      (sourceIso R X Y f U V g hU hV haU haV hg).hom ≫
        (G).map (HomologicalComplex.homologyMap (ModuleCechTrace.trace R X Y f V g) g) := by
  let W : ι × κ → Y.left.Opens := fun a => U a.1 ⊓ V a.2
  have hW : ⨆ i, W i = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show y ∈ ⨆ i, U i by rw [hU]; trivial)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (show y ∈ ⨆ j, V j by rw [hV]; trivial)
    exact Opens.mem_iSup.mpr ⟨(i,j), hi, hj⟩
  have haW (a : ι × κ) : IsAffineOpen (W a) := (haU a.1).inf (haV a.2)
  let r₁ : FormalCoproduct.mk (ι × κ) W ⟶ FormalCoproduct.mk ι U :=
    ⟨Prod.fst, fun _ => homOfLE inf_le_left⟩
  let r₂ : FormalCoproduct.mk (ι × κ) W ⟶ FormalCoproduct.mk κ V :=
    ⟨Prod.snd, fun _ => homOfLE inf_le_right⟩
  let W₃ := IntrinsicDeRham.CechTransfer.Intrinsic.inverseCover R X Y f W
  exact square
    (sourceIso R X Y f U V g hU hV haU haV hg).hom
    (sourceIso R X Y f V W g hV hW haV haW hg).hom
    (sourceIso R X Y f U W g hU hW haU haW hg).hom
    (ModuleCech.PositiveCover.Comparison.iso R Y U V hU hV haU haV N g hg).hom
    (ModuleCech.PositiveCover.Comparison.iso R Y V W hV hW haV haW N g hg).hom
    (ModuleCech.PositiveCover.Comparison.iso R Y U W hU hW haU haW N g hg).hom
    ((G).map (HomologicalComplex.homologyMap (ModuleCechTrace.trace R X Y f U g) g))
    ((G).map (HomologicalComplex.homologyMap (ModuleCechTrace.trace R X Y f V g) g))
    ((G).map (HomologicalComplex.homologyMap (ModuleCechTrace.trace R X Y f W g) g))
    (ModuleCech.PositiveTransitivity.hom_comp R X W₁ W₂ W₃ _ _ _ _ _ _ M g hg)
    (ModuleCech.PositiveTransitivity.hom_comp R Y U V W hU hV hW haU haV haW N g hg)
    (ModuleTraceRefinement.cohomology R X Y f U W r₁ g hU hW haU haW hg)
    (ModuleTraceRefinement.cohomology R X Y f V W r₂ g hV hW haV haW hg)

theorem trace (x : IntrinsicDeRham.TopEdge.Intrinsic.source R X W₁ g) :
    (ModuleCech.PositiveCover.Comparison.iso R Y U V hU hV haU haV N g hg).hom
        (IntrinsicDeRham.TopEdgeTransfer.Intrinsic.trace R X Y f U g x) =
      IntrinsicDeRham.TopEdgeTransfer.Intrinsic.trace R X Y f V g
        ((sourceIso R X Y f U V g hU hV haU haV hg).hom x) := by
  have h := ConcreteCategory.congr_hom (cohomology R X Y f U V g hU hV haU haV hg) x
  change (ModuleCech.PositiveCover.Comparison.iso R Y U V hU hV haU haV N g hg).hom
      (HomologicalComplex.homologyMap (ModuleCechTrace.trace R X Y f U g) g x) =
    HomologicalComplex.homologyMap (ModuleCechTrace.trace R X Y f V g) g _ at h
  rw [ModuleTraceHomology.top_trace, ModuleTraceHomology.top_trace] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ModuleTraceCoverNaturality
