import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.SupportCycles
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CycleMaps

/-! # Proper Support Cycles -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.ProperSupportCycles

noncomputable section

/-! Proper positioning on one integral component remains proper
after its native cycle embedding. Supports on other components cannot
contribute a nonempty intersection. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CycleMaps

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (K : irreducibleComponents X.carrier)

theorem contained (A B C : IrreducibleCloseds X.carrier) (hA : (A : Set X.carrier) ⊆ K.val)
    (hC : (C : Set X.carrier) ⊆ (A : Set X.carrier) ∩ (B : Set X.carrier)) :
    (B : Set X.carrier) ⊆ K.val := by
  have hCK : (C : Set X.carrier) ⊆ K.val := fun x hx => hA (hC hx).1
  have hCL : (C : Set X.carrier) ⊆ (X.supportComponent B).val :=
    fun x hx => X.support_subset_component B (hC hx).2
  have he : X.supportComponent B = K :=
    (X.supportComponent_eq_of_subset C (X.supportComponent B) hCL).symm.trans
      (X.supportComponent_eq_of_subset C K hCK)
  exact he ▸ X.support_subset_component B

theorem codimension (W : IrreducibleCloseds X.carrier) (hW : (W : Set X.carrier) ⊆ K.val) :
    (X.componentVariety K).presentation.supportCodimension (X.componentSupportPreimage K W hW) =
      X.supportCodimension W := by
  rw [← Image.image_codimension, X.componentSupportImage_preimage]

variable {τ : Type} (Z : τ → IrreducibleCloseds X.carrier)

abbrev index := {t : τ // (Z t : Set X.carrier) ⊆ K.val}

def family (t : index X K Z) : IrreducibleCloseds (X.componentVariety K).presentation.carrier :=
  X.componentSupportPreimage K (Z t.val) t.property

theorem embed (p : ℕ) (a : (X.componentVariety K).presentation.RationalDimensionCycle p)
    (ha : a ∈ Proper.SupportCycles.submodule (X.componentVariety K).presentation p (family X K Z)) :
    CycleMaps.embed X K p a ∈ Proper.SupportCycles.submodule X p Z := by
  intro t B hB C hC
  have hBn : Finsupp.mapDomain (Image.supportImage X K p) a B ≠ 0 := Finsupp.mem_support_iff.mp hB
  obtain ⟨B', rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero hBn
  have hB' : B' ∈ a.support := by
    apply Finsupp.mem_support_iff.mpr
    simpa only [Finsupp.mapDomain_apply_of_injective (Image.supportImage_injective X K p)] using hBn
  have hZ : (Z t : Set X.carrier) ⊆ K.val :=
    contained X K _ (Z t) C (X.componentSupportImage_subset K B'.val) hC
  have hCK : (C : Set X.carrier) ⊆ K.val :=
    fun x hx => X.componentSupportImage_subset K B'.val (hC hx).1
  let C' := X.componentSupportPreimage K C hCK
  have hin : (C' : Set (X.componentVariety K).presentation.carrier) ⊆
      (B'.val : Set (X.componentVariety K).presentation.carrier) ∩
        (family X K Z ⟨t, hZ⟩ : Set (X.componentVariety K).presentation.carrier) := by
    intro x hx
    change X.componentInclusion K x ∈ (C : Set X.carrier) at hx
    refine ⟨?_, (hC hx).2⟩
    obtain ⟨y, hy, he⟩ := (hC hx).1
    exact (X.componentInclusion K).isEmbedding.injective he ▸ hy
  have hb := ha ⟨t, hZ⟩ B' hB' C' hin
  change p + (X.componentVariety K).presentation.supportCodimension (X.componentSupportPreimage K (Z t) hZ) ≤
    (X.componentVariety K).presentation.supportCodimension (X.componentSupportPreimage K C hCK) at hb
  rwa [codimension, codimension] at hb

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.ProperSupportCycles
