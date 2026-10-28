import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBaseTmul
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechPullbackComponents
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechScalarComponents

/-! # Cech Base Change Components -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBaseChangeComponents

noncomputable section

/-! The canonical tensor comparison before extension of scalars, on each Cech intersection. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.CechBaseChangeMap

private theorem equality_π {Y S : Scheme.{u}} {p r : Y ⟶ S} (h : p = r)
    (M : Y.Modules) {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens)
    (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q) :
    (eqToHom (congrArg (fun p => SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex p M U) h)).f q ≫
      Pi.π (fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor r M U q j.1) i =
    Pi.π (fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor p M U q j.1) i ≫
      eqToHom (congrArg (fun p => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor p M U q i.1) h) := by
  cases h
  simp only [eqToHom_refl, HomologicalComplex.id_f, Category.id_comp, Category.comp_id]

variable {X Y S T : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
variable (h : f ≫ π = ρ ≫ g) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

def factorMap (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q) : SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U q i.1 ⟶
    (ModuleCat.restrictScalars g.appTop.hom).obj
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor ρ ((Scheme.Modules.pullback f).obj M) (fun j => f ⁻¹ᵁ U j) q i.1) :=
  ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).map ((pullbackPushforwardAdjunction f).unit.app M)).app
      (op (∏ᶜ fun k => U (i.1 k))) ≫
    (SheafCohomology.Projective.OrderedBaseCechPushforward.Scheme.Modules.baseCechFactorPushforwardIso f π ((Scheme.Modules.pullback f).obj M) U q i.1).inv ≫
    eqToHom (congrArg (fun p => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor p ((Scheme.Modules.pullback f).obj M)
      (fun j => f ⁻¹ᵁ U j) q i.1) h) ≫
    (BaseScalar.Construction.BaseScalarRestriction.sectionsIso ρ g ((Scheme.Modules.pullback f).obj M)
      (∏ᶜ fun k => f ⁻¹ᵁ U (i.1 k))).hom

private theorem paste {C : Type*} [Category C]
    {A B D E A' B' D' E' : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    (p : A ⟶ A') (q : B ⟶ B') (r : D ⟶ D') (s : E ⟶ E')
    (a' : A' ⟶ B') (b' : B' ⟶ D') (c' : D' ⟶ E')
    (ha : a ≫ q = p ≫ a') (hb : b ≫ r = q ≫ b') (hc : c ≫ s = r ≫ c') :
    (a ≫ b ≫ c) ≫ s = p ≫ a' ≫ b' ≫ c' := by
  simp only [Category.assoc]
  rw [hc, ← Category.assoc b, hb, Category.assoc, ← Category.assoc a, ha]
  simp only [Category.assoc]

theorem restricted_component_π (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q) :
    (CechBaseTmul.Construction.CechBaseChangeMap.restrictedMap f π ρ g h M U).f q ≫
      (ModuleCat.restrictScalars g.appTop.hom).map
        (Pi.π (fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q =>
          SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor ρ ((Scheme.Modules.pullback f).obj M) (fun k => f ⁻¹ᵁ U k) q j.1) i) =
    Pi.π (fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U q j.1) i ≫
      factorMap f π ρ g h M U q i := by
  have ha := CechPullbackComponents.Construction.CechPullbackMap.component_π f π M U q i
  have hb := equality_π h ((Scheme.Modules.pullback f).obj M) (fun k => f ⁻¹ᵁ U k) q i
  have hc := CechScalarComponents.Construction.CechScalarRestriction.object_π ρ g ((Scheme.Modules.pullback f).obj M)
    (fun k => f ⁻¹ᵁ U k) q i
  have H := paste _ _ _ _ _ _ _ _ _ _ ha hb hc
  simpa only [CechBaseTmul.Construction.CechBaseChangeMap.restrictedMap, factorMap, HomologicalComplex.comp_f, CechScalarCoface.Construction.CechScalarRestriction.complexIso,
    HomologicalComplex.Hom.isoOfComponents_hom_f, Category.assoc] using H

end Construction.CechBaseChangeMap

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBaseChangeComponents
