import OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.ExtensionOf
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ExtPushout

/-! # Extension Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology

noncomputable section

/-! Coefficient maps on actual degree-one extensions and their local sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.FormalGeometry.Completion.ExtPushout.Construction

universe u
variable {X : Scheme.{u}} {F G : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
  (E : ExtensionOf.CohomologyExtension.Extension X F) (f : F ⟶ G)

def ExtensionOf.CohomologyExtension.Extension.map : ExtensionOf.CohomologyExtension.Extension X G where
  middle := (AlgebraicGeometry.FormalGeometry.Completion.ExtPushout.Construction.pushoutExtensionComplex E.complex f).X₂
  inclusion := (AlgebraicGeometry.FormalGeometry.Completion.ExtPushout.Construction.pushoutExtensionComplex E.complex f).f
  projection := (AlgebraicGeometry.FormalGeometry.Completion.ExtPushout.Construction.pushoutExtensionComplex E.complex f).g
  zero := (AlgebraicGeometry.FormalGeometry.Completion.ExtPushout.Construction.pushoutExtensionComplex E.complex f).zero
  shortExact := AlgebraicGeometry.FormalGeometry.Completion.ExtPushout.Construction.pushoutExtensionComplex_shortExact E.shortExact f

theorem ExtensionOf.CohomologyExtension.Extension.map_extClass : (E.map f).extClass = Sheaf.H.map f 1 E.extClass :=
  AlgebraicGeometry.FormalGeometry.Completion.ExtPushout.Construction.pushoutExtensionComplex_extClass E.shortExact f

def ExtensionOf.CohomologyExtension.Extension.mapFiber (U : X.ProEt) (s : E.Fiber U) : (E.map f).Fiber U :=
  ⟨(pushout.inl E.inclusion f).hom.app (op U) s.val, by
    have h := congrArg (fun k : E.middle ⟶ AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant X => k.hom.app (op U) s.val)
      (pushout.inl_desc (f := E.inclusion) (g := f) E.projection 0
        (by rw [E.zero, comp_zero]))
    exact h.trans s.property⟩

theorem ExtensionOf.CohomologyExtension.Extension.mapFiber_restrict {U V : X.ProEt} (g : V ⟶ U) (s : E.Fiber U) :
    (E.map f).restrict g (E.mapFiber f U s) = E.mapFiber f V (E.restrict g s) := by
  apply Subtype.ext
  exact (NatTrans.naturality_apply (pushout.inl E.inclusion f).hom g.op s.val).symm

theorem ExtensionOf.CohomologyExtension.Extension.mapFiber_eq_of_difference (U : X.ProEt) (s t : E.Fiber U)
    (a : F.obj.obj (op U)) (ha : E.inclusion.hom.app (op U) a + s.val = t.val)
    (hz : f.hom.app (op U) a = 0) : E.mapFiber f U s = E.mapFiber f U t := by
  apply Subtype.ext
  have h := congrArg ((pushout.inl E.inclusion f).hom.app (op U)) ha
  have hw := congrArg (fun k : F ⟶ (E.map f).middle => k.hom.app (op U) a)
    (pushout.condition (f := E.inclusion) (g := f))
  change (pushout.inl E.inclusion f).hom.app (op U) (E.inclusion.hom.app (op U) a) =
    (E.map f).inclusion.hom.app (op U) (f.hom.app (op U) a) at hw
  rw [map_add, hw, hz, map_zero] at h
  erw [zero_add] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology
