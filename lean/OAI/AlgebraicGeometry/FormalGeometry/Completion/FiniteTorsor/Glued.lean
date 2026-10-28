import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.GluingData

/-! # Glued -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

noncomputable section

/-!
# Completion: the glued torsor scheme is finite étale over the original base

Relative gluing recovers the affine pieces by actual pullback squares.
Finiteness and étaleness then follow by their Zariski locality on the target.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}} {ℓ n : ℕ} [NeZero (ℓ ^ n)]
  (E : App.Construction.FiniteCoefficientExtension ℓ n X)

theorem App.Construction.FiniteCoefficientExtension.gluedSchemeToBase_finite : IsFinite E.gluedSchemeToBase := by
  apply IsZariskiLocalAtTarget.of_openCover X.directedAffineCover
  intro i
  let h := (E.relativeGluingData.isPullback_natTrans_ι_toBase i).flip
  have : IsFinite (E.relativeGluingData.natTrans.app i) :=
    E.affineSliceObject_finite ((GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i)
  change IsFinite (pullback.snd E.relativeGluingData.toBase (X.directedAffineCover.f i))
  rw [← h.isoPullback_inv_snd]
  infer_instance

theorem App.Construction.FiniteCoefficientExtension.gluedSchemeToBase_etale : Etale E.gluedSchemeToBase := by
  apply IsZariskiLocalAtTarget.of_openCover X.directedAffineCover
  intro i
  let h := (E.relativeGluingData.isPullback_natTrans_ι_toBase i).flip
  have : Etale (E.relativeGluingData.natTrans.app i) :=
    E.affineSliceObject_etale ((GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i)
  change Etale (pullback.snd E.relativeGluingData.toBase (X.directedAffineCover.f i))
  rw [← h.isoPullback_inv_snd]
  infer_instance

/-- The glued finite étale scheme is an object of the actual pro-étale site. -/
def App.Construction.FiniteCoefficientExtension.gluedProEt : X.ProEt := by
  have := E.gluedSchemeToBase_etale
  exact Scheme.ProEt.mk E.gluedSchemeToBase

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor
