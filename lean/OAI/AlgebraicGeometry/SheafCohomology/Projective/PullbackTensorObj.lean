/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PullbackTensorGeneral

/-! # Pullback Tensor Obj -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PullbackTensorObj.Scheme.Modules

open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules

/-!
# Pullback commutes with the sheafified tensor (general morphisms)

The general-`f` closure of `[PIC-P1b-MONO]`'s last registered leaf, relocated from
`Picard/InvertibleSheaf.lean` (which cannot import the monoidal-pullback machinery — the
import chain runs the other way): for any morphism of schemes `f: Y ⟶ X` and
`𝒪ₓ`-modules `M, N`,

`f^*(M ⊗ N) ≅ f^*M ⊗ f^*N`

for the sheafified tensor `tensorObj` of `Picard/InvertibleSheaf.lean`. Assembled from
mathlib's `sheafificationCompPullback` (the pullback of a sheafification), the tensorator
of the monoidal presheaf pullback (`PresheafOfModules.pullbackMonoidal` — the
`[D-PresPB′-general]` payoff), and the double-sheafification collapse
`nonempty_sheafify_tensor_idem` (the D-Idem leaf).
-/

universe u

open _root_.CategoryTheory MonoidalCategory

variable {X Y : Scheme.{u}}

/-- Bridging instance: the monoidal structure on presheaves of modules over the
`sheafToPresheaf`-spelled underlying presheaf of the ring sheaf (the clothing produced by
`Sheaf.Hom.hom`-projections), transported from the `CommRingCat`-derived clothing. -/
noncomputable instance (X : Scheme.{u}) : MonoidalCategory
    (_root_.PresheafOfModules.{u}
      ((sheafToPresheaf (Opens.grothendieckTopology ↥X) RingCat).obj
        X.ringCatSheaf)) :=
  inferInstanceAs (MonoidalCategory
    (_root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))

set_option backward.isDefEq.respectTransparency.types false in
/-- The pullback of a sheaf of modules is the sheafification of the presheaf pullback of
its underlying presheaf (`sheafificationCompPullback`, precomposed with the counit
identification `sh(M.val) ≅ M`). -/
noncomputable def pullbackIsoSheafifyPresheafPullback (f : Y ⟶ X) (M : X.Modules) :
    (Modules.pullback f).obj M ≅
      (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
        ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj M.val) :=
  (Modules.pullback f).mapIso (Invertible.Scheme.Modules.sheafifyValIso M).symm ≪≫
    (SheafOfModules.sheafificationCompPullback.{u} f.toRingCatSheafHom).app M.val

set_option backward.isDefEq.respectTransparency.types false in
/-- **(GAP-1 downstream core, general `f`, closed.)** Pullback commutes with the
sheafified tensor: `f^*(M ⊗ N) ≅ f^*M ⊗ f^*N`. Relocated from
`Picard/InvertibleSheaf.lean` and proved: express both sides through the sheafification
of the presheaf pullback (`pullbackIsoSheafifyPresheafPullback`), apply the tensorator of
the monoidal presheaf pullback, and collapse the double sheafification
(`nonempty_sheafify_tensor_idem`). -/
theorem nonempty_pullback_tensorObj (f : Y ⟶ X) (M N : X.Modules) :
    Nonempty ((Modules.pullback f).obj (Invertible.Scheme.Modules.tensorObj M N) ≅
      Invertible.Scheme.Modules.tensorObj ((Modules.pullback f).obj M) ((Modules.pullback f).obj N)) := by
  -- Pulling back the sheafified tensor gives the sheafification of the
  -- presheaf pullback of the presheaf tensor.
  have pullbackTensorSheafificationIso : (Modules.pullback f).obj (Invertible.Scheme.Modules.tensorObj M N) ≅
      (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
        ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj (M.val ⊗ N.val)) :=
    (SheafOfModules.sheafificationCompPullback.{u} f.toRingCatSheafHom).app (M.val ⊗ N.val)
  -- The monoidal presheaf pullback supplies the tensor comparison in the
  -- definitionally equal `CommRingCat` presentation used here.
  obtain ⟨presheafPullbackTensorIso⟩ := PullbackTensorGeneral.Scheme.Modules.nonempty_sheafify_presheafPullback_tensor f M.val N.val
  -- Idempotence collapses the repeated sheafification.
  obtain ⟨repeatedSheafificationTensorIso⟩ := PullbackTensorMonoidal.PresheafOfModules.nonempty_sheafify_tensor_idem
    Y.sheaf.obj Y.ringCatSheaf.property
    ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj M.val)
    ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj N.val)
  -- Finally, identify the sheafified factors with the module pullbacks.
  have sheafifiedFactorsPullbackIso : Invertible.Scheme.Modules.tensorObj
      ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
        ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj M.val))
      ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
        ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj N.val)) ≅
      Invertible.Scheme.Modules.tensorObj ((Modules.pullback f).obj M) ((Modules.pullback f).obj N) :=
    Invertible.Scheme.Modules.tensorObjCongr (pullbackIsoSheafifyPresheafPullback f M).symm
      (pullbackIsoSheafifyPresheafPullback f N).symm
  exact ⟨pullbackTensorSheafificationIso ≪≫ presheafPullbackTensorIso ≪≫
    repeatedSheafificationTensorIso ≪≫ sheafifiedFactorsPullbackIso⟩

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PullbackTensorObj.Scheme.Modules
