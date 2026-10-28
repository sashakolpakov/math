import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.BaseChange

noncomputable section

/-!
# Open base change for module sheaves in PoincareBundle

Direct image commutes with restriction to an open subscheme. The
isomorphism is constructed on sections using the equality of the two
inverse-image open sets.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

/-- The source module sheaf for open base change. -/
abbrev source (M : X.Modules) : U.toScheme.Modules :=
  (Scheme.Modules.restrictFunctor U.ι).obj ((Scheme.Modules.pushforward f).obj M)

/-- The target module sheaf for open base change. -/
abbrev target (M : X.Modules) : U.toScheme.Modules :=
  (Scheme.Modules.pushforward (f ∣_ U)).obj
    ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj M)

/-- The sectionwise open-base-change isomorphism respects scalar multiplication. -/
def sectionIso (M : X.Modules) (W : U.toScheme.Opens) :
    ((source f U M).val.obj (op W)) ≅ ((target f U M).val.obj (op W)) := by
  let h := image_morphismRestrict_preimage f U W
  refine ModuleCat.isoMk (M.presheaf.mapIso (eqToIso h).op) ?_
  intro r
  ext m
  change (M.smul (U := (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ W))
      (((f ⁻¹ᵁ U).ι.appIso ((f ∣_ U) ⁻¹ᵁ W)).inv
        ((f ∣_ U).app W r))).hom (M.presheaf.map (eqToHom h).op m) =
    M.presheaf.map (eqToHom h).op
      ((M.smul (U := f ⁻¹ᵁ (U.ι ''ᵁ W))
        (f.app (U.ι ''ᵁ W) ((U.ι.appIso W).inv r))).hom m)
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
  rw [morphismRestrict_app]
  exact (M.map_smul (eqToHom h) (f.app (U.ι ''ᵁ W) r) m).symm

@[simp]
theorem sectionIso_hom_apply (M : X.Modules) (W : U.toScheme.Opens)
    (m : (source f U M).val.obj (op W)) :
    (sectionIso f U M W).hom m =
      M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U W)).op m := rfl

/-- Direct image and open restriction agree on each module sheaf. -/
def pushforwardRestrictObjIso (M : X.Modules) : source f U M ≅ target f U M := by
  apply (Scheme.Modules.fullyFaithfulToPresheafOfModules (X := U)).preimageIso
  refine PresheafOfModules.isoMk (fun W => sectionIso f U M W.unop) ?_
  intro V W i
  ext m
  have heq :
      (TopologicalSpace.Opens.map f.base).op.map (U.ι.opensFunctor.op.map i) ≫
          (eqToIso (image_morphismRestrict_preimage f U W.unop)).op.hom =
        (eqToIso (image_morphismRestrict_preimage f U V.unop)).op.hom ≫
          (f ⁻¹ᵁ U).ι.opensFunctor.op.map
            ((TopologicalSpace.Opens.map (f ∣_ U).base).op.map i) := Subsingleton.elim _ _
  have hm := congrArg (fun k => M.presheaf.map k m) heq
  change (M.presheaf.map
      ((TopologicalSpace.Opens.map f.base).op.map (U.ι.opensFunctor.op.map i)) ≫
        M.presheaf.map (eqToIso (image_morphismRestrict_preimage f U W.unop)).op.hom) m =
    (M.presheaf.map (eqToIso (image_morphismRestrict_preimage f U V.unop)).op.hom ≫
      M.presheaf.map ((f ⁻¹ᵁ U).ι.opensFunctor.op.map
        ((TopologicalSpace.Opens.map (f ∣_ U).base).op.map i))) m
  simpa only [Functor.map_comp] using hm

/-- The open-base-change identification is natural in the module sheaf. -/
def pushforwardRestrictIso :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward (f ∣_ U) := by
  refine NatIso.ofComponents (pushforwardRestrictObjIso f U) ?_
  intro M N a
  apply Scheme.Modules.hom_ext
  intro W
  ext m
  exact congrArg (fun b => b m) (a.mapPresheaf.naturality
    (eqToHom (image_morphismRestrict_preimage f U W)).op).symm

/-- Geometric pullback commutes with restriction to the corresponding
open subschemes. -/
def pullbackRestrictIso :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
      (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι) ≪≫
    Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f ≪≫
    Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm ≪≫
    (Scheme.Modules.pullbackComp (f ∣_ U) U.ι).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
      (Scheme.Modules.pullback (f ∣_ U))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.BaseChange
