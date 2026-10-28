import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechPullbackHomology

/-! # Cech Pullback Components -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechPullbackComponents

noncomputable section

/-! The canonical pullback chain map evaluated on each ordered Cech factor. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.CechPullbackMap

private theorem inv_square {C : Type*} [Category C]
    {A B X Y : C} (e : A ≅ B) (k : X ≅ Y) (s : A ⟶ X) (t : B ⟶ Y)
    (h : e.hom ≫ t = s ≫ k.hom) : e.inv ≫ s = t ≫ k.inv := by
  apply (cancel_mono k.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

variable {X Y S : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

private theorem object_map_π {M N : X.Modules} (a : M ⟶ N) (q : ℕ)
    (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q) :
    (SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechObjectFunctor π U q).map a ≫
      Pi.π (fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π N U q j.1) i =
    Pi.π (fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U q j.1) i ≫
      ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).map a).app (op (∏ᶜ fun k => U (i.1 k))) :=
  Pi.map_π (fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q =>
    ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).map a).app (op (∏ᶜ fun k => U (j.1 k)))) i

theorem component_π (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q) :
    (CechPullbackHomology.Construction.CechPullbackMap.map f π M U).f q ≫
      Pi.π (fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q =>
        SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor (f ≫ π) ((Scheme.Modules.pullback f).obj M) (fun k => f ⁻¹ᵁ U k) q j.1) i =
    Pi.π (fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U q j.1) i ≫
      ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).map ((pullbackPushforwardAdjunction f).unit.app M)).app
        (op (∏ᶜ fun k => U (i.1 k))) ≫
      (SheafCohomology.Projective.OrderedBaseCechPushforward.Scheme.Modules.baseCechFactorPushforwardIso f π ((Scheme.Modules.pullback f).obj M) U q i.1).inv := by
  let P := (Scheme.Modules.pullback f).obj M
  let a := (SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechObjectFunctor π U q).map ((pullbackPushforwardAdjunction f).unit.app M)
  let e := SheafCohomology.Projective.OrderedBaseCechPushforward.Scheme.Modules.orderedBaseCechObjectPushforwardIso f π P U q
  let b := Pi.π (fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q =>
    SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor (f ≫ π) P (fun k => f ⁻¹ᵁ U k) q j.1) i
  let c := Pi.π (fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q =>
    SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π ((pushforward f).obj P) U q j.1) i
  let k := SheafCohomology.Projective.OrderedBaseCechPushforward.Scheme.Modules.baseCechFactorPushforwardIso f π P U q i.1
  have he : e.inv ≫ b = c ≫ k.inv :=
    inv_square e k b c (SheafCohomology.Projective.OrderedBaseCechPushforward.Scheme.Modules.orderedBaseCechObjectPushforwardIso_hom_π f π P U q i)
  change (a ≫ e.inv) ≫ b = _
  rw [Category.assoc, he, ← Category.assoc]
  exact congrArg (fun z => z ≫ k.inv)
    (object_map_π π U ((pullbackPushforwardAdjunction f).unit.app M) q i) |>.trans
      (Category.assoc _ _ _)

end Construction.CechPullbackMap

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechPullbackComponents
