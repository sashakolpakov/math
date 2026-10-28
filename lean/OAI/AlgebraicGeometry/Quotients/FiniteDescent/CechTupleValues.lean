import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechTuplePi

/-! # Cech Tuple Values -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechTupleValues

noncomputable section

/-! Explicit restriction formulas for the first three Cech coordinate maps. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.CechTupleCoordinates

variable {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
variable {ι : Type u} (U : ι → X.Opens)

def value (q : ℕ) (z : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X q) (a : Fin (q + 1) → ι) :
    SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U q a :=
  Pi.π (fun i : Fin (q + 1) → ι => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U q i) a z

theorem pi_value (q : ℕ) (z : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X q) (a : Fin (q + 1) → ι) :
    (SheafCohomology.Projective.BaseCechProducts.Scheme.Modules.baseCechXIsoPi π M U q).hom z a = value π M U q z a :=
  ConcreteCategory.congr_hom (ModuleCat.piIsoPi_hom_ker_subtype
    (fun i : Fin (q + 1) → ι => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U q i) a) z

theorem zero_apply (z : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X 0) (i : ι) :
    CechTuplePi.Construction.CechTupleCoordinates.zero π M U z i = M.presheaf.map (eqToHom (CechTuplePi.Construction.CechTupleCoordinates.intersection_zero U i).symm).op
      (value π M U 0 z (fun _ => i)) := by
  exact congrArg (fun t => M.presheaf.map (eqToHom (CechTuplePi.Construction.CechTupleCoordinates.intersection_zero U i).symm).op t)
    (pi_value π M U 0 z (fun _ => i))

theorem one_apply (z : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X 1) (i j : ι) :
    CechTuplePi.Construction.CechTupleCoordinates.one π M U z i j = M.presheaf.map (eqToHom (CechTuplePi.Construction.CechTupleCoordinates.intersection_one U (i, j)).symm).op
      (value π M U 1 z ![i, j]) := by
  exact congrArg (fun t => M.presheaf.map (eqToHom (CechTuplePi.Construction.CechTupleCoordinates.intersection_one U (i, j)).symm).op t)
    (pi_value π M U 1 z ![i, j])

theorem two_apply (z : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X 2) (i j k : ι) :
    CechTuplePi.Construction.CechTupleCoordinates.two π M U z i j k = M.presheaf.map (eqToHom (CechTuplePi.Construction.CechTupleCoordinates.intersection_two U (i, j, k)).symm).op
      (value π M U 2 z ![i, j, k]) := by
  exact congrArg (fun t => M.presheaf.map (eqToHom (CechTuplePi.Construction.CechTupleCoordinates.intersection_two U (i, j, k)).symm).op t)
    (pi_value π M U 2 z ![i, j, k])

end Construction.CechTupleCoordinates

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechTupleValues
