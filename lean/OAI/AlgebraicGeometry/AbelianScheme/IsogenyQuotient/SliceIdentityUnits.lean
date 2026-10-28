import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SliceTorsionCoordinates

/-! # Slice Identity Units -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SliceIdentityUnits.Construction

noncomputable section

/-! The iterated-slice comparison is the identity on the underlying
scheme, so its actual pullback acts identically on regular units. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem parameterSliceTestIso_units {S : Scheme.{u}} (Q : Over S) (V : Over Q)
    (z : Γ(V.left.left, ⊤)ˣ) : Units.map (SliceKernelPoints.Construction.parameterSliceTestIso Q V).hom.left.appTop.hom.toMonoidHom z = z := by
  apply Units.ext
  change Scheme.Hom.appTop (𝟙 V.left.left) z.val = z.val
  rw [Scheme.Hom.id_appTop]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SliceIdentityUnits.Construction
