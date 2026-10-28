import OAI.RepresentationTheory.Theta.Geometric.LineBundleIsoGluing

/-! # Framed Unit Isomorphisms -/

namespace OAI.RepresentationTheory.Theta.Geometric.FramedUnitIsomorphisms

noncomputable section

/-! Local isomorphisms defined by native frames and regular units. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

local instance (X : Scheme.{u}) : ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) := fun U => by
  change IsMulCommutative (X.presheaf.obj U)
  exact IsMulCommutative.of_comm fun a b => mul_comm a b

def overUnitIso {X : Scheme.{u}} (U : X.Opens) (r : Γ(X, U)ˣ) :
    _root_.SheafOfModules.unit (X.ringCatSheaf.over U) ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U) :=
  Aut.unitsEndEquivAut _ (Units.map
    (AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEndRingHom X.ringCatSheaf U).toMonoidHom r)

theorem overScalar_comp {X : Scheme.{u}} (U : X.Opens) (r s : Γ(X, U)) :
    AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r ≫
      AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U s =
    AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U (r * s) := by
  have h := (AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEndRingHom X.ringCatSheaf U).map_mul s r
  change _ = _ ≫ _ at h
  exact h.symm.trans (congrArg (fun t : Γ(X, U) => AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U t)
    (mul_comm s r))

def framedUnitIso {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (g : N.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (r : Γ(X, U)ˣ) : M.over U ≅ N.over U :=
  e ≪≫ overUnitIso U r ≪≫ g.symm

theorem framedUnitIso_eq_of_transitions {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (e₀ e₁ : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (g₀ g₁ : N.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (a b : Γ(X, U)) (r s : Γ(X, U)ˣ)
    (he : e₀.hom = e₁.hom ≫ AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U a)
    (hg : g₀.hom = g₁.hom ≫ AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U b)
    (hr : a * (r : Γ(X, U)) = (s : Γ(X, U)) * b) :
    (framedUnitIso M N U e₀ g₀ r).hom = (framedUnitIso M N U e₁ g₁ s).hom := by
  apply (cancel_mono g₀.hom).1
  change (e₀.hom ≫ AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U (r : Γ(X, U)) ≫ g₀.inv) ≫ g₀.hom =
    (e₁.hom ≫ AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U (s : Γ(X, U)) ≫ g₁.inv) ≫ g₀.hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hg, Iso.inv_hom_id_assoc, he]
  simp only [Category.assoc, overScalar_comp, hr]

end

end OAI.RepresentationTheory.Theta.Geometric.FramedUnitIsomorphisms
