import Mathlib.AlgebraicGeometry.RelativeGluing
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Gluing Closed Immersion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GluingClosedImmersion

noncomputable section

/-! Compatible closed chart embeddings glue to a closed immersion into the ambient scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem relativeGluing_toBase_closed
    {S : Scheme.{u}} (U : S.OpenCover) [Category U.I₀] [U.LocallyDirected]
    [Quiver.IsThin U.I₀] [Small.{u} U.I₀] (d : U.RelativeGluingData)
    [∀ i, IsClosedImmersion (d.natTrans.app i)] : IsClosedImmersion d.toBase := by
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) U).mpr
  intro i
  let H := (d.isPullback_natTrans_ι_toBase i).flip
  have hc : IsClosedImmersion (H.isoPullback.inv ≫ d.natTrans.app i) := IsClosedImmersion.comp _ _
  have he : H.isoPullback.inv ≫ d.natTrans.app i = U.pullbackHom d.toBase i := H.isoPullback_inv_snd
  exact (congrArg IsClosedImmersion he).mp hc

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GluingClosedImmersion
