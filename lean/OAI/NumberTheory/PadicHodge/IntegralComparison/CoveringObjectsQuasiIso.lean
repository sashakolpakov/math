import OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringObjectsSheafDetection
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConservativeExactFamily

/-! # Covering Objects Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringObjectsQuasiIso

noncomputable section

/-! Quasi-isomorphisms of module sheaf complexes are detected on covering objects. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v z

variable {C : Type (max u v)} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type (max u v)) [CommRing R]

local instance restriction_additive (U : C) : (J.overPullback (ModuleCat.{max u v} R) U).Additive where
  map_add := by intros; rfl

local instance restriction_leftAdjoint (U : C) : (J.overPullback (ModuleCat.{max u v} R) U).IsLeftAdjoint :=
  ((Over.forget U).sheafAdjunctionCocontinuous (ModuleCat.{max u v} R) (J.over U) J).isLeftAdjoint

local instance restriction_limits (U : C) : PreservesFiniteLimits (J.overPullback (ModuleCat.{max u v} R) U) :=
  by infer_instance

local instance restriction_colimits (U : C) : PreservesFiniteColimits (J.overPullback (ModuleCat.{max u v} R) U) :=
  by infer_instance

variable {ι : Type z} (F : ι → C)
  (hcover : ∀ U, CoveringObjectsSheafDetection.sieve F U ∈ J U)

include hcover in
theorem quasiIso_complex {α : Type*} {c : ComplexShape α}
    {K L : HomologicalComplex (Sheaf J (ModuleCat.{max u v} R)) c} (f : K ⟶ L)
    (hf : ∀ i, QuasiIso (((J.overPullback (ModuleCat.{max u v} R) (F i)).mapHomologicalComplex c).map f)) :
    QuasiIso f :=
  ConservativeExactFamily.Family.quasiIso_complex (fun i => J.overPullback (ModuleCat.{max u v} R) (F i))
    (fun H hH => CoveringObjectsSheafDetection.isZero J F R hcover H hH) f hf

include hcover in
theorem quasiIso {K L : CochainComplex (Sheaf J (ModuleCat.{max u v} R)) ℕ} (f : K ⟶ L)
    (hf : ∀ i, QuasiIso (((J.overPullback (ModuleCat.{max u v} R) (F i)).mapHomologicalComplex (.up ℕ)).map f)) :
    QuasiIso f := quasiIso_complex J R F hcover f hf

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringObjectsQuasiIso
