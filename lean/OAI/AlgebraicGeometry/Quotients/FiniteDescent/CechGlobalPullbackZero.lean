import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBaseChangeFactors
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechSquare

/-! # Cech Global Pullback Zero -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechGlobalPullbackZero

noncomputable section

/-! Vanishing of the pullback of a global section is detected on its
actual ordered Cech zero-cochain. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.CechBaseChangeMap

private theorem product_ext {R : Type u} [CommRing R] {I : Type u}
    (A : I → ModuleCat.{u} R) {x y : (∏ᶜ A : ModuleCat.{u} R)}
    (h : ∀ i, Pi.π A i x = Pi.π A i y) : x = y := by
  apply (ModuleCat.mono_iff_injective (ModuleCat.piIsoPi A).hom).mp inferInstance
  funext i
  exact (ConcreteCategory.congr_hom (ModuleCat.piIsoPi_hom_ker_subtype A i) x).trans
    ((h i).trans (ConcreteCategory.congr_hom (ModuleCat.piIsoPi_hom_ker_subtype A i) y).symm)

variable {X Y S T : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
variable (h : f ≫ π = ρ ≫ g) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

theorem restricted_global_zero (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op ⊤))
    (hs : PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M ⊤ s = 0) :
    (CechBaseTmul.Construction.CechBaseChangeMap.restrictedMap f π ρ g h M U).f 0 (OrderedCechSquare.Construction.OrderedCechAugmentation.map π M U s) = 0 := by
  let A : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 → ModuleCat.{u} Γ(S, ⊤) :=
    fun j => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 j.1
  let B : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 → ModuleCat.{u} Γ(T, ⊤) :=
    fun j => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor ρ ((Scheme.Modules.pullback f).obj M) (fun k => f ⁻¹ᵁ U k) 0 j.1
  apply product_ext B
  intro i
  change Pi.π B i ((CechBaseTmul.Construction.CechBaseChangeMap.restrictedMap f π ρ g h M U).f 0
    (OrderedCechSquare.Construction.OrderedCechAugmentation.map π M U s)) = Pi.π B i 0
  rw [map_zero]
  have hp := ConcreteCategory.congr_hom (CechBaseChangeComponents.Construction.CechBaseChangeMap.restricted_component_π f π ρ g h M U 0 i)
    (OrderedCechSquare.Construction.OrderedCechAugmentation.map π M U s)
  change Pi.π B i ((CechBaseTmul.Construction.CechBaseChangeMap.restrictedMap f π ρ g h M U).f 0
    (OrderedCechSquare.Construction.OrderedCechAugmentation.map π M U s)) =
      CechBaseChangeComponents.Construction.CechBaseChangeMap.factorMap f π ρ g h M U 0 i (Pi.π A i (OrderedCechSquare.Construction.OrderedCechAugmentation.map π M U s)) at hp
  have ha := ConcreteCategory.congr_hom (OrderedCechSquare.Construction.OrderedCechAugmentation.map_π π M U i) s
  change Pi.π A i (OrderedCechSquare.Construction.OrderedCechAugmentation.map π M U s) =
    M.presheaf.map (homOfLE (show (∏ᶜ fun k => U (i.1 k)) ≤ ⊤ from le_top)).op s at ha
  rw [hp, ha, CechBaseChangeFactors.Construction.CechBaseChangeMap.factor_apply]
  have hr := PullbackSectionRestrict.Construction.PullbackSectionCoefficients.restrict f M
    (show (∏ᶜ fun k => U (i.1 k)) ≤ ⊤ from le_top) s
  rw [hs, map_zero] at hr
  rw [hr, map_zero]

end Construction.CechBaseChangeMap

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechGlobalPullbackZero
