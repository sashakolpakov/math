import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechScalarCoface

/-! # Cech Scalar Components -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechScalarComponents

noncomputable section

/-! Restricting base scalars acts componentwise on ordered Cech cochains. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.CechScalarRestriction

private theorem inverse_projection {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {I : Type u} (P : I → C) [HasProduct P]
    [HasProduct (fun i => F.obj (P i))] [IsIso (piComparison F P)] (i : I) :
    (asIso (piComparison F P)).inv ≫ F.map (Pi.π P i) =
      Pi.π (fun j => F.obj (P j)) i := by
  rw [← piComparison_comp_π F P i, ← Category.assoc]
  exact (congrArg (fun z => z ≫ Pi.π (fun j => F.obj (P j)) i)
    (asIso (piComparison F P)).inv_hom_id).trans (Category.id_comp _)

variable {X T S : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ S) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

theorem object_π (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q) :
    (CechScalarCoface.Construction.CechScalarRestriction.objectIso f g M U q).hom ≫ (ModuleCat.restrictScalars g.appTop.hom).map
      (Pi.π (fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor f M U q j.1) i) =
    Pi.π (fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor (f ≫ g) M U q j.1) i ≫
      (BaseScalar.Construction.BaseScalarRestriction.sectionsIso f g M (∏ᶜ fun k => U (i.1 k))).hom := by
  let F := ModuleCat.restrictScalars g.appTop.hom
  let P : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q → ModuleCat.{u} Γ(T, ⊤) :=
    fun j => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor f M U q j.1
  let A : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q → ModuleCat.{u} Γ(S, ⊤) :=
    fun j => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor (f ≫ g) M U q j.1
  let a : ∀ j, A j ⟶ F.obj (P j) :=
    fun j => (BaseScalar.Construction.BaseScalarRestriction.sectionsIso f g M (∏ᶜ fun k => U (j.1 k))).hom
  change (Limits.Pi.map a ≫ (asIso (piComparison F P)).inv) ≫ F.map (Pi.π P i) = _
  rw [Category.assoc, inverse_projection]
  exact Pi.map_π a i

end Construction.CechScalarRestriction

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechScalarComponents
