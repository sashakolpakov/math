import Mathlib.Topology.Sheaves.Functors

/-! # Image Cech Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Inverse.ImageCechCover

/-! The literal inverse-image opens form a cover for every continuous map. -/

open _root_.CategoryTheory _root_.TopologicalSpace

theorem inverseImageCechCover_covers {X Y : TopCat.{0}} (f : X ⟶ Y)
    {I : Type} (U : I → Opens Y) (hU : iSup U = ⊤) :
    (⨆ i, (Opens.map f).obj (U i)) = ⊤ := by
  apply top_unique
  intro x _
  have hx : f x ∈ iSup U := hU.symm ▸ show f x ∈ (⊤ : Opens Y) from trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Inverse.ImageCechCover
