import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBaseChangeFactors
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechSquare

/-! # Global Section Cech Pullback -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback

noncomputable section

/-! Actual pullback of global sections agrees with the canonical Cech
pullback on degree-zero cochains, with all open restrictions explicit. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

namespace Construction

universe u

theorem restrictedPullbackSection_restriction {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    {U U' : X.Opens} {V V' : Y.Opens} (hU : U' ≤ U) (hV : V' ≤ V)
    (h : V ≤ f ⁻¹ᵁ U) (h' : V' ≤ f ⁻¹ᵁ U') (s : Γ(M, U)) :
    ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hV).op
      (Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map f M U V h s) =
      Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map f M U' V' h' (M.presheaf.map (homOfLE hU).op s) := by
  unfold Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map
  rw [Quotients.FiniteDescent.PullbackSectionRestrict.Construction.PullbackSectionCoefficients.restrict,
    ← CategoryTheory.Functor.map_comp_apply, ← CategoryTheory.Functor.map_comp_apply]
  congr 1

def globalLineSectionPullback {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (s : Γ(M, ⊤)) : Γ((Scheme.Modules.pullback f).obj M, ⊤) :=
  Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map f M ⊤ ⊤ (by simp) s

private theorem product_ext {R : Type u} [CommRing R] {I : Type u}
    (A : I → ModuleCat.{u} R) {x y : (∏ᶜ A : ModuleCat.{u} R)}
    (h : ∀ i, Pi.π A i x = Pi.π A i y) : x = y := by
  apply (ModuleCat.piIsoPi A).toLinearEquiv.injective
  funext i
  exact (ConcreteCategory.congr_hom (ModuleCat.piIsoPi_hom_ker_subtype A i) x).trans
    ((h i).trans (ConcreteCategory.congr_hom (ModuleCat.piIsoPi_hom_ker_subtype A i) y).symm)

theorem cechPullback_globalSection
    {X Y S T : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
    (h : f ≫ π = ρ ≫ g) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op ⊤)) :
    (Quotients.FiniteDescent.CechBaseTmul.Construction.CechBaseChangeMap.restrictedMap f π ρ g h M U).f 0 (Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map π M U s) =
      Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map ρ ((Scheme.Modules.pullback f).obj M) (fun i => f ⁻¹ᵁ U i)
        (globalLineSectionPullback f M s) := by
  let A : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 → ModuleCat.{u} Γ(S, ⊤) := fun i => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 i.1
  let B : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 → ModuleCat.{u} Γ(T, ⊤) :=
    fun i => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor ρ ((Scheme.Modules.pullback f).obj M) (fun k => f ⁻¹ᵁ U k) 0 i.1
  apply product_ext B
  intro i
  have hp := ConcreteCategory.congr_hom (Quotients.FiniteDescent.CechBaseChangeComponents.Construction.CechBaseChangeMap.restricted_component_π f π ρ g h M U 0 i)
    (Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map π M U s)
  change Pi.π B i ((Quotients.FiniteDescent.CechBaseTmul.Construction.CechBaseChangeMap.restrictedMap f π ρ g h M U).f 0
    (Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map π M U s)) =
    Quotients.FiniteDescent.CechBaseChangeComponents.Construction.CechBaseChangeMap.factorMap f π ρ g h M U 0 i (Pi.π A i (Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map π M U s)) at hp
  rw [hp]
  rw [show Pi.π A i (Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map π M U s) =
    M.presheaf.map (homOfLE (show (∏ᶜ fun k => U (i.1 k)) ≤ ⊤ from le_top)).op s from
      ConcreteCategory.congr_hom (Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map_π π M U i) s]
  rw [Quotients.FiniteDescent.CechBaseChangeFactors.Construction.CechBaseChangeMap.factor_apply]
  have ht := ConcreteCategory.congr_hom
    (Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map_π ρ ((Scheme.Modules.pullback f).obj M) (fun k => f ⁻¹ᵁ U k) i)
    (globalLineSectionPullback f M s)
  change Pi.π B i
      (Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map ρ ((Scheme.Modules.pullback f).obj M) (fun k => f ⁻¹ᵁ U k)
        (globalLineSectionPullback f M s)) =
    ((Scheme.Modules.pullback f).obj M).presheaf.map
      (homOfLE (show (∏ᶜ fun k => f ⁻¹ᵁ U (i.1 k)) ≤ ⊤ from le_top)).op
        (globalLineSectionPullback f M s) at ht
  rw [ht]
  exact (restrictedPullbackSection_restriction f M le_top le_top (by simp)
    (le_of_eq ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Hom.preimage_cechIntersection f) U 0 i.1).symm) s).symm

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback
