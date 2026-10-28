import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBaseChangeFactors
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechSquare

/-! # Cech Pullback Section Normalization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CechPullbackSectionNormalization

noncomputable section

/-! Canonical pullback of a global section agrees with pullback of its
actual ordered Cech zero-cochain, including top-open transport. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

def pullbackTopSection {X Y : Scheme.{u}} (a : Y ⟶ X) (M : X.Modules)
    (s : Γ(M, ⊤)) : Γ((Scheme.Modules.pullback a).obj M, ⊤) :=
  ((Scheme.Modules.pullback a).obj M).presheaf.map (eqToHom a.preimage_top.symm).op
    (Quotients.FiniteDescent.PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map a M ⊤ s)

theorem cech_restricted_global_eq_pullback
    {X Y S T : Scheme.{u}} (a : Y ⟶ X) (f : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
    (h : a ≫ f = ρ ≫ g) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f M).obj (op ⊤)) :
    (Quotients.FiniteDescent.CechBaseTmul.Construction.CechBaseChangeMap.restrictedMap a f ρ g h M U).f 0
      (Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map f M U s) =
      Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map ρ ((Scheme.Modules.pullback a).obj M)
        (fun i => a ⁻¹ᵁ U i) (pullbackTopSection a M s) := by
  let A : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 → ModuleCat.{u} Γ(S, ⊤) :=
    fun j => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor f M U 0 j.1
  let B : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 → ModuleCat.{u} Γ(T, ⊤) :=
    fun j => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor ρ ((Scheme.Modules.pullback a).obj M) (fun k => a ⁻¹ᵁ U k) 0 j.1
  apply (ModuleCat.mono_iff_injective (ModuleCat.piIsoPi B).hom).mp inferInstance
  funext i
  change Pi.π B i _ = Pi.π B i _
  have hp := ConcreteCategory.congr_hom
    (Quotients.FiniteDescent.CechBaseChangeComponents.Construction.CechBaseChangeMap.restricted_component_π a f ρ g h M U 0 i)
    (Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map f M U s)
  change Pi.π B i ((Quotients.FiniteDescent.CechBaseTmul.Construction.CechBaseChangeMap.restrictedMap a f ρ g h M U).f 0
    (Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map f M U s)) =
      Quotients.FiniteDescent.CechBaseChangeComponents.Construction.CechBaseChangeMap.factorMap a f ρ g h M U 0 i
        (Pi.π A i (Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map f M U s)) at hp
  rw [hp]
  rw [show Pi.π A i (Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map f M U s) =
      M.presheaf.map (homOfLE (show (∏ᶜ fun k => U (i.1 k)) ≤ ⊤ from le_top)).op s from
      ConcreteCategory.congr_hom (Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map_π f M U i) s]
  rw [Quotients.FiniteDescent.CechBaseChangeFactors.Construction.CechBaseChangeMap.factor_apply, Quotients.FiniteDescent.PullbackSectionRestrict.Construction.PullbackSectionCoefficients.restrict]
  have ht := ConcreteCategory.congr_hom (Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map_π ρ
    ((Scheme.Modules.pullback a).obj M) (fun k => a ⁻¹ᵁ U k) i) (pullbackTopSection a M s)
  change Pi.π B i (Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map ρ ((Scheme.Modules.pullback a).obj M)
      (fun k => a ⁻¹ᵁ U k) (pullbackTopSection a M s)) =
    ((Scheme.Modules.pullback a).obj M).presheaf.map
      (homOfLE (show (∏ᶜ fun k => a ⁻¹ᵁ U (i.1 k)) ≤ ⊤ from le_top)).op
        (pullbackTopSection a M s) at ht
  rw [ht]
  dsimp only [pullbackTopSection]
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  exact ConcreteCategory.congr_hom
    (((Scheme.Modules.pullback a).obj M).presheaf.congr_map (Subsingleton.elim _ _)) _

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CechPullbackSectionNormalization
