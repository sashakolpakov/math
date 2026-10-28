import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.FrameScalars

/-! # Unit Section Transport -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.UnitSectionTransport

noncomputable section

/-! Transport of unit powers through section-ring isomorphisms,
including the inverse convention for frame transitions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem sectionIso_unit_inverse_power {R S : CommRingCat.{u}} (e : R ≅ S) (c : Sˣ) (d : ℤ) :
    e.hom ((((Units.map e.inv.hom.toMonoidHom c) ^ d)⁻¹ : Rˣ) : R) = ((c ^ (-d) : Sˣ) : S) := by
  have hc : Units.map e.hom.hom.toMonoidHom (Units.map e.inv.hom.toMonoidHom c) = c := by
    apply Units.ext
    exact Iso.inv_hom_id_apply e (c : S)
  change ((Units.map e.hom.hom.toMonoidHom
    (((Units.map e.inv.hom.toMonoidHom c) ^ d)⁻¹)) : S) = _
  rw [← zpow_neg, map_zpow, hc]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.UnitSectionTransport
