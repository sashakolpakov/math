import Mathlib.Data.Set.Countable

/-! # Countable Fiber Images -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.CountableFiberImages

/-! Countably many countable images of code fibers cover the image. -/

theorem countable_range_of_countable_code_fiber_images
    {I C X : Type*} [Countable C] (code : I → C) (p : I → X)
    (h : ∀ c, (Set.range (fun i : {i : I // code i = c} => p i)).Countable) :
    (Set.range p).Countable := by
  apply (Set.countable_iUnion h).mono
  rintro _ ⟨i, rfl⟩
  exact Set.mem_iUnion.mpr ⟨code i, ⟨⟨i, rfl⟩, rfl⟩⟩

end OAI.AlgebraicGeometry.PELModuli.CMPoints.CountableFiberImages
