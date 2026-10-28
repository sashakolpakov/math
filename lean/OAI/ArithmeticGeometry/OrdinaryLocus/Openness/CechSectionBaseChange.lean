import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenPullbackSections
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GlobalModel
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBaseChangeFactors

/-! # Cech Section Base Change -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CechSectionBaseChange.Construction

noncomputable section

/-! The ordered Cech base-change map agrees with canonical pullback of global sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped ChangeOfRings

universe u

private theorem moduleProduct_element_ext {R : Type u} [CommRing R] {I : Type u}
    (A : I → ModuleCat.{u} R) {x y : (∏ᶜ A : ModuleCat.{u} R)}
    (h : ∀ i, Pi.π A i x = Pi.π A i y) : x = y := by
  apply (ModuleCat.mono_iff_injective (ModuleCat.piIsoPi A).hom).mp inferInstance
  funext i
  exact (ConcreteCategory.congr_hom (ModuleCat.piIsoPi_hom_ker_subtype A i) x).trans
    ((h i).trans (ConcreteCategory.congr_hom (ModuleCat.piIsoPi_hom_ker_subtype A i) y).symm)

variable {X Y S T : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
variable (h : f ≫ π = ρ ≫ g) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

theorem orderedCech_pullback_augmentation (s : (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op ⊤)) :
    (AlgebraicGeometry.Quotients.FiniteDescent.CechBaseTmul.Construction.CechBaseChangeMap.restrictedMap f π ρ g h M U).f 0
      (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map π M U s) =
    AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map ρ ((Scheme.Modules.pullback f).obj M)
      (fun i ↦ f ⁻¹ᵁ U i) (OpenPullbackSections.Construction.modulePullbackSection f M ⊤ s) := by
  let A : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 → ModuleCat.{u} Γ(S, ⊤) :=
    fun j ↦ AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 j.1
  let B : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 → ModuleCat.{u} Γ(T, ⊤) :=
    fun j ↦ AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor ρ ((Scheme.Modules.pullback f).obj M) (fun k ↦ f ⁻¹ᵁ U k) 0 j.1
  apply moduleProduct_element_ext B
  intro i
  have hp := ConcreteCategory.congr_hom
    (AlgebraicGeometry.Quotients.FiniteDescent.CechBaseChangeComponents.Construction.CechBaseChangeMap.restricted_component_π f π ρ g h M U 0 i)
    (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map π M U s)
  have ha := ConcreteCategory.congr_hom (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map_π π M U i) s
  have hb := ConcreteCategory.congr_hom
    (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map_π ρ ((Scheme.Modules.pullback f).obj M)
      (fun j ↦ f ⁻¹ᵁ U j) i) (OpenPullbackSections.Construction.modulePullbackSection f M ⊤ s)
  change Pi.π B i ((AlgebraicGeometry.Quotients.FiniteDescent.CechBaseTmul.Construction.CechBaseChangeMap.restrictedMap f π ρ g h M U).f 0
    (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map π M U s)) =
      AlgebraicGeometry.Quotients.FiniteDescent.CechBaseChangeComponents.Construction.CechBaseChangeMap.factorMap f π ρ g h M U 0 i
        (Pi.π A i (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map π M U s)) at hp
  change Pi.π A i (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map π M U s) =
    M.presheaf.map (homOfLE (show (∏ᶜ fun k ↦ U (i.1 k)) ≤ ⊤ from le_top)).op s at ha
  change Pi.π B i (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map ρ
    ((Scheme.Modules.pullback f).obj M) (fun j ↦ f ⁻¹ᵁ U j)
      (OpenPullbackSections.Construction.modulePullbackSection f M ⊤ s)) =
    ((Scheme.Modules.pullback f).obj M).presheaf.map
      (homOfLE (show (∏ᶜ fun k ↦ f ⁻¹ᵁ U (i.1 k)) ≤ ⊤ from le_top)).op
        (OpenPullbackSections.Construction.modulePullbackSection f M ⊤ s) at hb
  rw [hp, ha, hb]
  refine (AlgebraicGeometry.Quotients.FiniteDescent.CechBaseChangeFactors.Construction.CechBaseChangeMap.factor_apply f π ρ g h M U 0 i
    (M.presheaf.map (homOfLE (show (∏ᶜ fun k ↦ U (i.1 k)) ≤ ⊤ from le_top)).op s)).trans ?_
  have hr := AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionRestrict.Construction.PullbackSectionCoefficients.restrict f M
    (show (∏ᶜ fun k ↦ U (i.1 k)) ≤ ⊤ from le_top) s
  refine (congrArg (fun z ↦ ((Scheme.Modules.pullback f).obj M).presheaf.map
    (eqToHom ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Hom.preimage_cechIntersection f) U 0 i.1).symm).op z) hr).trans ?_
  rw [← ((Scheme.Modules.pullback f).obj M).presheaf.map_comp_apply]
  rfl

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CechSectionBaseChange.Construction
