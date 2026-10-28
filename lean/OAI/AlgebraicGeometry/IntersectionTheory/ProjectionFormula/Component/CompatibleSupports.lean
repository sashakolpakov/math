import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.CompatibleMoving
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.ProperSupportCycles
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Bilinear

/-! # Compatible Supports -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CompatibleSupports

noncomputable section

/-! Fixed proper intersection constraints restrict to an integral
component and return under the native cycle embedding. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (K : irreducibleComponents X.carrier)
  (q : ℕ) {ι : Type} (B : ι → X.DimensionCycleSupport q)

abbrev index := {i : ι // ((B i).val : Set X.carrier) ⊆ K.val}

def family (i : index X K q B) : (X.componentVariety K).presentation.DimensionCycleSupport q :=
  Image.supportPreimage X K q (B i.val) i.property

theorem image (i : index X K q B) : Image.supportImage X K q (family X K q B i) = B i.val :=
  Image.supportImage_preimage X K q (B i.val) i.property

theorem restrict_proper (p : ℕ) (a : X.RationalDimensionCycle p)
    (hproper : ∀ W ∈ a.support, ∀ i, ∀ C : IrreducibleCloseds X.carrier,
      (C : Set X.carrier) ⊆ (W.val : Set X.carrier) ∩ ((B i).val : Set X.carrier) → p + q ≤ X.supportCodimension C) :
    ∀ W ∈ (CycleMaps.restrict X K p a).support, ∀ i : index X K q B,
      ∀ C : IrreducibleCloseds (X.componentVariety K).presentation.carrier,
      (C : Set (X.componentVariety K).presentation.carrier) ⊆
        (W.val : Set (X.componentVariety K).presentation.carrier) ∩
        ((family X K q B i).val : Set (X.componentVariety K).presentation.carrier) →
          p + q ≤ (X.componentVariety K).presentation.supportCodimension C := by
  intro W hW i
  have hWa : Image.supportImage X K p W ∈ a.support := by
    rw [Finsupp.mem_support_iff, ← CycleMaps.restrict_apply]
    exact Finsupp.mem_support_iff.mp hW
  apply (Bilinear.PairCycle.pair_proper_image X K p q W (family X K q B i)).mp
  rw [image]
  exact hproper (Image.supportImage X K p W) hWa i.val

theorem embed_position {τ : Type} (Z : τ → IrreducibleCloseds X.carrier) (p : ℕ)
    (a : (X.componentVariety K).presentation.RationalDimensionCycle p)
    (hproper : a ∈ Proper.SupportCycles.submodule (X.componentVariety K).presentation p
      (Sum.elim (ProperSupportCycles.family X K Z) (fun i => (family X K q B i).val))) :
    CycleMaps.embed X K p a ∈ Proper.SupportCycles.submodule X p (Sum.elim Z (fun i => (B i).val)) := by
  apply ProperSupportCycles.embed X K (Sum.elim Z (fun i => (B i).val)) p a
  intro t W hW C hC
  obtain ⟨t, ht⟩ := t
  cases t with
  | inl t => exact hproper (Sum.inl ⟨t, ht⟩) W hW C hC
  | inr i => exact hproper (Sum.inr ⟨i, ht⟩) W hW C hC

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CompatibleSupports
