import OAI.AlgebraicGeometry.SheafCohomology.Projective.CanonicalAffineFrame
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Evaluation

/-! # Over Generator -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.OverGenerator

noncomputable section

/-! Compatibility of a specified generator with the open-subscheme equivalence. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)

def overGeneratorHom (s : Γ(M, U)) :
    _root_.SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ M.over U :=
  (M.over U).unitHomEquiv.symm (Evaluation.SheafOfModules.overSection X.ringCatSheaf M U s)

theorem overGeneratorHom_app (s : Γ(M, U)) (V : Over U)
    (a : X.presheaf.obj (op V.left)) :
    (overGeneratorHom M U s).val.app (op V) a =
      a • M.presheaf.map V.hom.op s := rfl

theorem overGeneratorHom_comp {N : X.Modules} (s : Γ(M, U)) (f : M ⟶ N) :
    overGeneratorHom M U s ≫ f.over U =
      overGeneratorHom N U (f.val.app (op U) s) := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change f.val.app (op V.unop.left)
    ((show Γ(X, V.unop.left) from a) • M.presheaf.map V.unop.hom.op s) =
      (show Γ(X, V.unop.left) from a) •
        N.presheaf.map V.unop.hom.op (f.val.app (op U) s)
  rw [(f.val.app (op V.unop.left)).hom.map_smul]
  congr 1
  exact PresheafOfModules.naturality_apply f.val V.unop.hom.op s

theorem overGeneratorHom_restriction (s : Γ(M, U)) :
    (Scheme.Modules.overEquiv U).functor.map (overGeneratorHom M U s) ≫
      ((Scheme.Modules.overFunctorEquiv U).app M).hom =
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom ≫
      CanonicalAffineFrame.openGeneratorHom M U s := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (show Γ(X, (U.overEquivalence.inverse.obj V.unop).left) from a) •
    M.presheaf.map (U.overEquivalence.inverse.obj V.unop).hom.op s =
    (CanonicalAffineFrame.openGeneratorHom M U s).val.app V (show Γ(U.toScheme, V.unop) from a)
  rw [CanonicalAffineFrame.openGeneratorHom, AffineRankOne.globalGeneratorHom_app]
  change (show Γ(X, (U.overEquivalence.inverse.obj V.unop).left) from a) •
      M.presheaf.map (U.overEquivalence.inverse.obj V.unop).hom.op s =
    (M.restrictAppIso U.ι V.unop).hom
      ((show Γ(U.toScheme, V.unop) from a) •
        (M.restrict U.ι).presheaf.map V.unop.leTop.op ((CanonicalAffineFrame.restrictionTopIso M U).inv s))
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply, Scheme.Opens.ι_appIso]
  simp only [CanonicalAffineFrame.restrictionTopIso, Iso.trans_inv, Functor.mapIso_inv,
    ConcreteCategory.comp_apply, Scheme.Modules.restrictAppIso]
  change (show Γ(X, (U.overEquivalence.inverse.obj V.unop).left) from a) •
      M.presheaf.map (U.overEquivalence.inverse.obj V.unop).hom.op s =
    (show Γ(X, U.ι ''ᵁ V.unop) from a) •
      M.presheaf.map (U.ι.opensFunctor.map V.unop.leTop).op
        (M.presheaf.map (eqToHom U.ι_image_top).op s)
  rw [← M.presheaf.map_comp_apply]
  congr 2

/-- A restriction frame defined by a section has that same generator over the
over-site. -/
theorem overTrivialization_inv_eq_overGenerator (s : Γ(M, U))
    (e : Invertible.Scheme.Modules.unitObj U.toScheme ≅ M.restrict U.ι)
    (he : e.hom = CanonicalAffineFrame.openGeneratorHom M U s) :
    (Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e.symm).inv =
      overGeneratorHom M U s := by
  let G := (Scheme.Modules.overEquiv U).functor
  let F := (Scheme.Modules.overFunctorEquiv U).app M
  apply G.map_injective
  apply (cancel_mono F.hom).1
  dsimp only [Invertible.Scheme.Modules.overTrivializationOfRestrictIso]
  rw [Functor.FullyFaithful.preimageIso_inv, Functor.FullyFaithful.map_preimage]
  change ((U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom ≫ e.hom ≫ F.inv) ≫
    F.hom = G.map (overGeneratorHom M U s) ≫ F.hom
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, he]
  exact (overGeneratorHom_restriction M U s).symm

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.OverGenerator
