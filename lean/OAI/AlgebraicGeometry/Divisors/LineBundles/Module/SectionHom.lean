import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GlobalFrame

/-! # Section Hom -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Module.SectionHom.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: a genuine global module section defines a morphism from the structure module -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} (M : X.Modules) (s : Γ(M, ⊤))

def moduleGlobalSectionFamily : M.sections :=
  PresheafOfModules.sectionsMk
    (fun U => M.presheaf.map (homOfLE le_top).op s)
    (fun {U V} i => by
      change M.presheaf.map i (M.presheaf.map (homOfLE le_top).op s) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)

def moduleSectionHom : DivisorClass.Chern.Line.Bundles.Construction.structureModule X ⟶ M :=
  M.unitHomEquiv.symm (moduleGlobalSectionFamily M s)

theorem moduleSectionHom_app_one (U : X.Opens) :
    (moduleSectionHom M s).app U (1 : Γ(X, U)) =
      M.presheaf.map (homOfLE le_top).op s := by
  exact congrArg (fun t : M.sections => t.val (Opposite.op U))
    (M.unitHomEquiv.apply_symm_apply (moduleGlobalSectionFamily M s))

theorem moduleSectionHom_app (U : X.Opens) (r : Γ(X, U)) :
    (moduleSectionHom M s).app U r = r • M.presheaf.map (homOfLE le_top).op s := rfl

theorem moduleSectionHom_app_top_one : (moduleSectionHom M s).app ⊤ (1 : Γ(X, ⊤)) = s := by
  rw [moduleSectionHom_app_one]
  change M.presheaf.map (𝟙 _) s = s
  rw [M.presheaf.map_id]
  rfl

end

/-! # LineBundleCycles: an actual section on an open subset defines a module morphism on that open scheme -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}}

theorem openInclusionImage_le (U : X.Opens) (W : U.toScheme.Opens) : U.ι ''ᵁ W ≤ U := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

def moduleSectionAsGlobal (M : X.Modules) (U : X.Opens) (s : Γ(M, U)) : Γ(M.restrict U.ι, ⊤) :=
  M.presheaf.map (homOfLE (openInclusionImage_le U ⊤)).op s

theorem moduleSectionAsGlobal_restrict (M : X.Modules) (U : X.Opens) (s : Γ(M, U))
    (W : U.toScheme.Opens) :
    (M.restrict U.ι).presheaf.map (homOfLE le_top).op (moduleSectionAsGlobal M U s) =
      M.presheaf.map (homOfLE (openInclusionImage_le U W)).op s := by
  change M.presheaf.map (homOfLE (U.ι.image_mono (show W ≤ ⊤ from le_top))).op
    (M.presheaf.map (homOfLE (openInclusionImage_le U ⊤)).op s) = _
  rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
  rfl

def moduleSectionHomOnOpen (M : X.Modules) (U : X.Opens) (s : Γ(M, U)) :
    DivisorClass.Chern.Line.Bundles.Construction.structureModule U.toScheme ⟶ M.restrict U.ι :=
  moduleSectionHom (M.restrict U.ι) (moduleSectionAsGlobal M U s)

theorem moduleSectionHomOnOpen_app (M : X.Modules) (U : X.Opens) (s : Γ(M, U))
    (W : U.toScheme.Opens) (r : Γ(U.toScheme, W)) :
    (moduleSectionHomOnOpen M U s).app W r =
      r • (M.restrict U.ι).presheaf.map (homOfLE le_top).op (moduleSectionAsGlobal M U s) :=
  moduleSectionHom_app (M.restrict U.ι) (moduleSectionAsGlobal M U s) W r

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Module.SectionHom.BundleCycles
