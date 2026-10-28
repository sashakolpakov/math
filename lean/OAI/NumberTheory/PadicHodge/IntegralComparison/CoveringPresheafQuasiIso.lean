import OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringObjectsQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.QuasiIsoFunctorIso

/-! # Covering Presheaf Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresheafQuasiIso

noncomputable section

/-! Objectwise local resolutions become genuine sheaf resolutions on a covering family of objects. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v z

variable {C : Type (max u v)} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type (max u v)) [CommRing R] {α : Type*} {c : ComplexShape α}
  {K L : HomologicalComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) c} (f : K ⟶ L)

theorem restricted (U : C)
    [QuasiIso ((((Functor.whiskeringLeft _ _ (ModuleCat.{max u v} R)).obj
      (Over.forget U).op).mapHomologicalComplex c).map f)] :
    QuasiIso (((J.overPullback (ModuleCat.{max u v} R) U).mapHomologicalComplex c).map
      (((presheafToSheaf J (ModuleCat.{max u v} R)).mapHomologicalComplex c).map f)) := by
  let T := (Functor.whiskeringLeft _ _ (ModuleCat.{max u v} R)).obj (Over.forget U).op
  let S := presheafToSheaf (J.over U) (ModuleCat.{max u v} R)
  let e := NatIso.mapHomologicalComplex
    ((Over.forget U).pushforwardContinuousSheafificationCompatibility
      (ModuleCat.{max u v} R) (J.over U) J) c
  let : QuasiIso (((T ⋙ S).mapHomologicalComplex c).map f) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology ((T.mapHomologicalComplex c).map f) S
  exact QuasiIsoFunctorIso.transport _ _ e f

variable {ι : Type z} (F : ι → C)
  (hcover : ∀ U, CoveringObjectsSheafDetection.sieve F U ∈ J U)

include hcover in
theorem quasiIso
    (hf : ∀ i, QuasiIso ((((Functor.whiskeringLeft _ _ (ModuleCat.{max u v} R)).obj
      (Over.forget (F i)).op).mapHomologicalComplex c).map f)) :
    QuasiIso (((presheafToSheaf J (ModuleCat.{max u v} R)).mapHomologicalComplex c).map f) := by
  apply CoveringObjectsQuasiIso.quasiIso_complex J R F hcover
  intro i
  let := hf i
  exact restricted J R f (F i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresheafQuasiIso
