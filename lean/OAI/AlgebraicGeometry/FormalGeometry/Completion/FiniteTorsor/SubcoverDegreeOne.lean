import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.ConstantTrivialization
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ConnectedConstantCover
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PullbackCompositionMap

/-! # Subcover Degree One -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

noncomputable section

/-! A connected component of an actual trivialized torsor base change has degree one. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y Z : Scheme.{u}} {ℓ n : ℕ} [NeZero (ℓ ^ n)]
  (E : App.Construction.FiniteCoefficientExtension ℓ n X)
  [PreconnectedSpace Y] [IsReduced Y]
  (f : Y ⟶ X) (g : Z ⟶ E.gluedScheme) [IsClosedImmersion g]
  [Etale (g ≫ E.gluedSchemeToBase)]
  [ConnectedSpace (pullback (g ≫ E.gluedSchemeToBase) f : Scheme.{u})]

/-- Vanishing of the actual pulled-back class, together with connectedness of the actual
closed subcover, makes its map to the base an isomorphism. -/
theorem App.Construction.FiniteCoefficientExtension.connectedSubcover_baseChange_isIso
    (h : Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n f 1 E.extClass = 0) :
    IsIso (pullback.snd (g ≫ E.gluedSchemeToBase) f) := by
  have : IsFinite E.gluedSchemeToBase := E.gluedSchemeToBase_finite
  let m := PullbackCompositionMap.Construction.pullbackCompositionMap E.gluedSchemeToBase g f
  let m' : Over.mk (pullback.snd (g ≫ E.gluedSchemeToBase) f) ⟶
      Over.mk (pullback.snd E.gluedSchemeToBase f) :=
    Over.homMk m (PullbackCompositionMap.Construction.pullbackCompositionMap_snd E.gluedSchemeToBase g f)
  let a : Over.mk (pullback.snd (g ≫ E.gluedSchemeToBase) f) ⟶
      AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme Y (ULift.{u} (ZMod (ℓ ^ n))) :=
    m' ≫ (E.baseChangeConstantIso f h).hom
  have : Mono a.left := by
    change Mono (m ≫ (E.baseChangeConstantIso f h).hom.left)
    infer_instance
  exact ConnectedConstantCover.Construction.connected_finiteEtale_subconstant_isIso (ULift.{u} (ZMod (ℓ ^ n)))
    (pullback.snd (g ≫ E.gluedSchemeToBase) f) a

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor
