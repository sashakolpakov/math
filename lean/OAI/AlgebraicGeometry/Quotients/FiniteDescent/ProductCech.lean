import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductFamilyCover
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineSectionOf

/-! # Product Cech -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductCech.Construction.ProductCechCoverProperties

noncomputable section

/-! Covering and affineness for the rectangles used in the product-family
Cech construction. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
variable {ι κ : Type u} (U : ι → X.Opens) (V : κ → Y.Opens)

include U V in
theorem covers (hU : iSup U = ⊤) (hV : iSup V = ⊤) :
    iSup (ProductFamilyCover.Construction.ProductFamilyAxes.cover f g U V) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show pullback.fst f g z ∈ iSup U by rw [hU]; trivial)
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (show pullback.snd f g z ∈ iSup V by rw [hV]; trivial)
  exact Opens.mem_iSup.mpr ⟨⟨i, j⟩, hi, hj⟩

theorem preimage_covers {T : Scheme.{u}} (p : T ⟶ X) (hU : iSup U = ⊤) :
    iSup (fun a => p ⁻¹ᵁ U a) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show p z ∈ iSup U by rw [hU]; trivial)
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

theorem affine [IsAffine S] (hU : ∀ a, IsAffineOpen (U a)) (hV : ∀ a, IsAffineOpen (V a)) :
    ∀ a, IsAffineOpen (ProductFamilyCover.Construction.ProductFamilyAxes.cover f g U V a) :=
  fun a => AffineSectionOf.Construction.AffineSectionCover.affine_pullback_open f g (hU a.1) (hV a.2)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductCech.Construction.ProductCechCoverProperties
