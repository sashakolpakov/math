import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomFunctoriality

/-! # Sheaf Hom Unit -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomUnit.Construction

noncomputable section

/-! The internal Hom out of the structure sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def moduleOverSectionsEquiv {X : Scheme.{u}} (N : X.Modules) (U : X.Opens) :
    (N.over U).sections ≃ Γ(N, U) where
  toFun s := s.val (.op (Over.mk (𝟙 U)))
  invFun n := PresheafOfModules.sectionsMk
    (fun V ↦ N.val.map V.unop.hom.op n)
    (by
      intro V W h
      have he : V.unop.hom.op ≫ h.unop.left.op = W.unop.hom.op :=
        congrArg Quiver.Hom.op (Over.w h.unop)
      have hm := (N.presheaf.map_comp V.unop.hom.op h.unop.left.op).symm.trans
        (congrArg N.presheaf.map he)
      exact congrArg (fun q ↦ q n) hm)
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro V
    exact PresheafOfModules.sections_property s
      (Over.homMk V.unop.hom : V.unop ⟶ Over.mk (𝟙 U)).op
  right_inv n := by
    change N.presheaf.map (𝟙 (.op U)) n = n
    simp

def moduleHomUnitSectionsEquiv {X : Scheme.{u}} (N : X.Modules) (U : X.Opens) :
    (ModuleHomAdditive.Construction.moduleHomLocalAddSubgroup (LineBundle.Construction.structureSheafModule X) N U) ≃ Γ(N, U) :=
  (ModuleHomSheaf.Construction.moduleHomOverEquiv (LineBundle.Construction.structureSheafModule X) N U).trans
    ((SheafOfModules.unitHomEquiv (N.over U)).trans (moduleOverSectionsEquiv N U))

theorem moduleHomUnitSectionsEquiv_apply {X : Scheme.{u}} (N : X.Modules) (U : X.Opens)
    (q : ModuleHomAdditive.Construction.moduleHomLocalAddSubgroup (LineBundle.Construction.structureSheafModule X) N U) :
    moduleHomUnitSectionsEquiv N U q = q.1.app (.op (Over.mk (𝟙 U))) (1 : Γ(X, U)) := rfl

def sheafHomUnitEvalAtOpen {X : Scheme.{u}} (N : X.Modules) (U : X.Opens) :
    (SheafHomModule.Construction.sheafHomModule (LineBundle.Construction.structureSheafModule X) N).val.obj (.op U) →ₗ[X.ringCatSheaf.obj.obj (.op U)]
      N.val.obj (.op U) where
  toFun := moduleHomUnitSectionsEquiv N U
  map_add' q q' := rfl
  map_smul' r q := by
    let r' : Γ(X, U) := r
    let z : Γ(N, U) := q.1.app (.op (Over.mk (𝟙 U))) (1 : Γ(X, U))
    change X.presheaf.map (𝟙 U).op r' • z = r' • z
    simp

def sheafHomUnitMap {X : Scheme.{u}} (N : X.Modules) :
    SheafHomModule.Construction.sheafHomModule (LineBundle.Construction.structureSheafModule X) N ⟶ N where
  val :=
    { app U := ModuleCat.ofHom (R := X.ringCatSheaf.obj.obj U)
        (X := (SheafHomModule.Construction.sheafHomModule (LineBundle.Construction.structureSheafModule X) N).val.obj U) (Y := N.val.obj U)
        (sheafHomUnitEvalAtOpen N U.unop)
      naturality {U V} h := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro q
        let j : Over.mk h.unop ⟶ Over.mk (𝟙 U.unop) := Over.homMk h.unop
        have hn := congrArg (fun a ↦ a (1 : Γ(X, U.unop))) (q.1.naturality j.op)
        change q.1.app (.op (Over.mk h.unop)) (X.presheaf.map h (1 : Γ(X, U.unop))) =
          N.presheaf.map h (q.1.app (.op (Over.mk (𝟙 U.unop))) (1 : Γ(X, U.unop))) at hn
        exact (congrArg (fun a ↦ q.1.app (.op (Over.mk h.unop)) a)
          ((X.presheaf.map h).hom.map_one)).symm.trans hn }

def sheafHomUnitIso {X : Scheme.{u}} (N : X.Modules) :
    SheafHomModule.Construction.sheafHomModule (LineBundle.Construction.structureSheafModule X) N ≅ N := by
  have : IsIso (sheafHomUnitMap N) := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    exact (moduleHomUnitSectionsEquiv N U).bijective
  exact asIso (sheafHomUnitMap N)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomUnit.Construction
