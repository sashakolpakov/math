import OAI.AlgebraicGeometry.Picard.Homomorphisms.FreePresheafTensor

/-! # Presheaf Generators -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.PresheafGenerators

noncomputable section

/-! Detecting natural isomorphisms of cocontinuous functors on free open generators. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {Y : Scheme.{u}} {D : Type*} [Category D]

theorem modulePresheafNatTrans_isIso_of_freeOpen
    {F G : Y.PresheafOfModules ⥤ D} (a : F ⟶ G)
    [PreservesColimitsOfSize.{u, u} F] [PreservesColimitsOfSize.{u, u} G]
    (h : ∀ U : Y.Opens, IsIso (a.app (FreePresheafTensor.Construction.freeOpenModulePresheaf Y U)))
    (M : Y.PresheafOfModules) : IsIso (a.app M) := by
  have hc (N : Y.PresheafOfModules) : IsIso (a.app N.freeYonedaCoproduct) := by
    let K := Discrete.functor (PresheafOfModules.Elements.freeYoneda (M := N))
    have (j : Discrete N.Elements) : IsIso ((Functor.whiskerLeft K a).app j) := h j.as.1.unop
    have : IsIso (Functor.whiskerLeft K a) := NatIso.isIso_of_isIso_app _
    exact isIso_app_coconePt_of_preservesColimit K a (colimit.cocone K) (colimit.isColimit K)
  have : PreservesColimitsOfSize.{0, 0} F := preservesSmallestColimits_of_preservesColimits F
  have : PreservesColimitsOfSize.{0, 0} G := preservesSmallestColimits_of_preservesColimits G
  let K := parallelPair M.toFreeYonedaCoproduct 0
  have (j : WalkingParallelPair) : IsIso ((Functor.whiskerLeft K a).app j) := by
    cases j <;> exact hc _
  have : IsIso (Functor.whiskerLeft K a) := NatIso.isIso_of_isIso_app _
  exact isIso_app_coconePt_of_preservesColimit K a
    M.freeYonedaCoproductsCokernelCofork M.isColimitFreeYonedaCoproductsCokernelCofork

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.PresheafGenerators
