import OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringObjectsSheafDetection
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-! # Covering Objects Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringObjectsProduct

noncomputable section

/-! Products of two genuine covering families form their common refinement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  (J : GrothendieckTopology C) {ι : Type w} {κ : Type z} (F : ι → C) (G : κ → C)

def family (i : ι × κ) := F i.1 ⨯ G i.2

theorem sieve (V : C) :
    CoveringObjectsSheafDetection.sieve (family F G) V =
      CoveringObjectsSheafDetection.sieve F V ⊓ CoveringObjectsSheafDetection.sieve G V := by
  ext W a
  constructor
  · rintro ⟨⟨i,j⟩, ⟨b⟩⟩
    exact ⟨⟨i, ⟨b ≫ prod.fst⟩⟩, ⟨j, ⟨b ≫ prod.snd⟩⟩⟩
  · rintro ⟨⟨i, ⟨b⟩⟩, ⟨j, ⟨c⟩⟩⟩
    exact ⟨⟨i,j⟩, ⟨prod.lift b c⟩⟩

theorem covering (hF : ∀ V, CoveringObjectsSheafDetection.sieve F V ∈ J V)
    (hG : ∀ V, CoveringObjectsSheafDetection.sieve G V ∈ J V) (V : C) :
    CoveringObjectsSheafDetection.sieve (family F G) V ∈ J V := by
  rw [sieve]
  exact J.intersection_covering (hF V) (hG V)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringObjectsProduct
