import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBaseChangeComponents
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionRestrict

/-! # Cech Base Change Factors -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBaseChangeFactors

noncomputable section

/-! Actual section formulas for the factor maps in Cech base change. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped ChangeOfRings

universe u

namespace Construction.CechBaseChangeMap

private theorem equality_apply {Y S : Scheme.{u}} {p r : Y ⟶ S} (h : p = r)
    (M : Y.Modules) (U : Y.Opens) (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf p M).obj (op U)) :
    eqToHom (congrArg (fun p => (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf p M).obj (op U)) h) s = s := by
  cases h
  rfl

variable {X Y S T : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
variable (h : f ≫ π = ρ ≫ g) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

theorem factor_apply (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q) (s : SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U q i.1) :
    CechBaseChangeComponents.Construction.CechBaseChangeMap.factorMap f π ρ g h M U q i s =
      ((Scheme.Modules.pullback f).obj M).presheaf.map
        (eqToHom ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Hom.preimage_cechIntersection f) U q i.1).symm).op
          (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M (∏ᶜ fun k => U (i.1 k)) s) :=
  equality_apply h ((Scheme.Modules.pullback f).obj M) (∏ᶜ fun k => f ⁻¹ᵁ U (i.1 k)) _

def tensorFactor (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q) :
    (ModuleCat.extendScalars g.appTop.hom).obj (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U q i.1) ⟶
      SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor ρ ((Scheme.Modules.pullback f).obj M) (fun j => f ⁻¹ᵁ U j) q i.1 :=
  ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).homEquiv _ _).symm
    (CechBaseChangeComponents.Construction.CechBaseChangeMap.factorMap f π ρ g h M U q i)

theorem tensorFactor_one (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q)
    (s : SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U q i.1) :
    tensorFactor f π ρ g h M U q i ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] s) =
      ((Scheme.Modules.pullback f).obj M).presheaf.map
        (eqToHom ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Hom.preimage_cechIntersection f) U q i.1).symm).op
          (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M (∏ᶜ fun k => U (i.1 k)) s) := by
  have he := ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).homEquiv _ _).apply_symm_apply
    (CechBaseChangeComponents.Construction.CechBaseChangeMap.factorMap f π ρ g h M U q i)
  exact (ConcreteCategory.congr_hom he s).trans (factor_apply f π ρ g h M U q i s)

end Construction.CechBaseChangeMap

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBaseChangeFactors
