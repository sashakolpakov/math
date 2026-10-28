/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleQuasicoherent.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentLocalization
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Module Global Sections Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModuleGlobalSectionsIsomorphism

noncomputable section

/-! Global sections detect isomorphisms of actual quasicoherent modules on affine schemes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules
universe u

theorem affineModule_isIso_of_globalSections_isIso
    {X : Scheme.{u}}
    [IsAffine X] {M N : X.Modules} (φ : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (h : IsIso (φ.val.app (.op (⊤ : X.Opens)))) : IsIso φ := by
  let F := Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor (RingHom.id Γ(X, ⊤))
  let φB := F.map φ
  let : IsIso (φ.val.app (.op (⊤ : X.Opens))) := h
  have hφBTop : IsIso (φB.app (.op (⊤ : X.Opens))) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ConcreteCategory.bijective_of_isIso
      (φ.val.app (.op (⊤ : X.Opens)))
  let hreflect : (SheafOfModules.toSheaf.{u}
      X.ringCatSheaf).ReflectsIsomorphisms :=
    PresheafOfModules.instReflectsIsomorphismsSheafOfModulesSheafAddCommGrpCatToSheaf_1
  have hmap : IsIso ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map φ) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis (isBasis_basicOpen X)
    intro r
    let V := X.basicOpen r
    let i := V.leTop.op
    let sourceRestriction := (F.obj M).map i
    let targetRestriction := (F.obj N).map i
    have hSource : IsLocalizedModule.Away r sourceRestriction.hom := by
      dsimp only [sourceRestriction, F, i, V]
      exact QuasicoherentLocalization.affine_quasicoherent_sections_localize M r
    have hTarget : IsLocalizedModule.Away r targetRestriction.hom := by
      dsimp only [targetRestriction, F, i, V]
      exact QuasicoherentLocalization.affine_quasicoherent_sections_localize N r
    have hφBOpen : IsIso (φB.app (.op V)) := by
      refine ModuleCat.isIso_of_isLocalizedModule_comp hSource ?_
      change IsLocalizedModule.Away r
        (sourceRestriction ≫ φB.app (.op V)).hom
      rw [φB.naturality i]
      change IsLocalizedModule.Away r
        (φB.app (.op (⊤ : X.Opens)) ≫ targetRestriction).hom
      exact IsLocalizedModule.of_linearEquiv_right
        (Submonoid.powers r) targetRestriction.hom
        (asIso (φB.app (.op (⊤ : X.Opens)))).toLinearEquiv
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ConcreteCategory.bijective_of_isIso (φB.app (.op V))
  exact @Functor.ReflectsIsomorphisms.reflects _ _ _ _
    (SheafOfModules.toSheaf.{u} X.ringCatSheaf) hreflect _ _ φ hmap

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModuleGlobalSectionsIsomorphism
