import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.Normalization

/-! # Affinization -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.Affinization.Construction

noncomputable section

/-! # Completion: proper affinization is surjective -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsAffine Y]

include f

/-- The map to the spectrum of global functions is proper over an affine proper base. -/
theorem proper_toSpecΓ : IsProper X.toSpecΓ := by
  have : IsProper (X.toSpecΓ ≫ Spec.map f.appTop) := by
    rw [← Scheme.toSpecΓ_naturality]
    infer_instance
  exact IsProper.of_comp X.toSpecΓ (Spec.map f.appTop)

/-- Properness and density make the actual affinization map surjective. -/
theorem proper_toSpecΓ_surjective : Surjective X.toSpecΓ := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := proper_toSpecΓ f
  constructor
  exact Set.range_eq_univ.mp (by
    rw [← X.toSpecΓ.isClosedMap.isClosed_range.closure_eq]
    exact X.toSpecΓ.denseRange.closure_range)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.Affinization.Construction
