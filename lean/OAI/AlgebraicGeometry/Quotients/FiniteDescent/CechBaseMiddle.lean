import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineCechBaseChange
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleCechPullbackShort
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechCoefficient
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionCongr

/-! # Cech Base Middle -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBaseMiddle

noncomputable section

/-! Canonical affine Cech base change commutes with restriction along a
morphism and a refinement of its cover, in degree one. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped ChangeOfRings

universe u

namespace Construction.CechBaseChangeRestriction

variable {X Y X' Y' S T : Scheme.{u}} [IsAffine S] [IsAffine T]
variable (i : Y ⟶ X) (p : X' ⟶ X) (q : Y' ⟶ Y) (j : Y' ⟶ X')
variable (π : X ⟶ S) (ρ : Y ⟶ S) (π' : X' ⟶ T) (ρ' : Y' ⟶ T) (g : T ⟶ S)
variable (hi : i ≫ π = ρ) (hj : j ≫ π' = ρ') (h : q ≫ i = j ≫ p)
variable (hp : IsPullback p π' π g) (hq : IsPullback q ρ' ρ g)
variable (M : X.Modules) [M.IsQuasicoherent]
variable [((Scheme.Modules.pullback i).obj M).IsQuasicoherent]
variable {ι κ : Type u} [Finite ι] [Finite κ]
variable (U : ι → X.Opens) (V : κ → Y.Opens) (r : κ → ι)
variable (hr : ∀ a, V a ≤ i ⁻¹ᵁ U (r a))
variable (hr' : ∀ a, q ⁻¹ᵁ V a ≤ j ⁻¹ᵁ (p ⁻¹ᵁ U (r a)))
variable (hU : ∀ a, IsAffineOpen (U a)) (hUU : ∀ a b, IsAffineOpen (U a ⊓ U b))
variable (hUUU : ∀ a b c, IsAffineOpen ((U a ⊓ U b) ⊓ U c))
variable (hV : ∀ a, IsAffineOpen (V a)) (hVV : ∀ a b, IsAffineOpen (V a ⊓ V b))
variable (hVVV : ∀ a b c, IsAffineOpen ((V a ⊓ V b) ⊓ V c))

def sourceIso := AffineCechBaseChange.Construction.OrdinaryAffineCechBaseChange.iso p π π' g hp M U hU hUU hUUU
def targetIso := AffineCechBaseChange.Construction.OrdinaryAffineCechBaseChange.iso q ρ ρ' g hq
  ((Scheme.Modules.pullback i).obj M) V hV hVV hVVV

def coefficientIso := (CechCoefficient.Construction.CechCoefficientFunctor.moduleFunctor ρ' (fun a => q ⁻¹ᵁ V a)).mapIso
  (PullbackSectionCongr.Construction.PullbackSectionSquare.iso i p q j h M)

theorem middle :
    (ModuleCat.extendScalars g.appTop.hom).map
        (ModuleCechPullbackShort.Construction.ModuleCechPullback.shortMap i π ρ hi M U V r hr).τ₂ ≫
      (targetIso i q ρ ρ' g hq M V hV hVV hVVV).hom.τ₂ ≫
        (coefficientIso i p q j ρ' h M V).hom.τ₂ =
    (sourceIso p π π' g hp M U hU hUU hUUU).hom.τ₂ ≫
      (ModuleCechPullbackShort.Construction.ModuleCechPullback.shortMap j π' ρ' hj ((Scheme.Modules.pullback p).obj M)
        (fun a => p ⁻¹ᵁ U a) (fun a => q ⁻¹ᵁ V a) r hr').τ₂ := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro z
  change (coefficientIso i p q j ρ' h M V).hom.τ₂
      ((targetIso i q ρ ρ' g hq M V hV hVV hVVV).hom.τ₂
        ((ModuleCat.extendScalars g.appTop.hom).map
          (ModuleCechPullbackShort.Construction.ModuleCechPullback.shortMap i π ρ hi M U V r hr).τ₂
            ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] z))) =
    (ModuleCechPullbackShort.Construction.ModuleCechPullback.shortMap j π' ρ' hj ((Scheme.Modules.pullback p).obj M)
      (fun a => p ⁻¹ᵁ U a) (fun a => q ⁻¹ᵁ V a) r hr').τ₂
        ((sourceIso p π π' g hp M U hU hUU hUUU).hom.τ₂
          ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] z))
  rw [ModuleCat.ExtendScalars.map_tmul]
  change (coefficientIso i p q j ρ' h M V).hom.τ₂
      ((AffineCechBaseChange.Construction.OrdinaryAffineCechBaseChange.iso q ρ ρ' g hq ((Scheme.Modules.pullback i).obj M)
        V hV hVV hVVV).hom.τ₂ ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom]
          ((ModuleCechPullbackShort.Construction.ModuleCechPullback.shortMap i π ρ hi M U V r hr).τ₂ z))) = _
  rw [AffineCechBaseChange.Construction.OrdinaryAffineCechBaseChange.middle_one]
  change _ = (ModuleCechPullbackShort.Construction.ModuleCechPullback.shortMap j π' ρ' hj ((Scheme.Modules.pullback p).obj M)
      (fun a => p ⁻¹ᵁ U a) (fun a => q ⁻¹ᵁ V a) r hr').τ₂
    ((AffineCechBaseChange.Construction.OrdinaryAffineCechBaseChange.iso p π π' g hp M U hU hUU hUUU).hom.τ₂
      ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] z))
  rw [AffineCechBaseChange.Construction.OrdinaryAffineCechBaseChange.middle_one]
  funext a b
  change (PullbackSectionCongr.Construction.PullbackSectionSquare.iso i p q j h M).hom.app (q ⁻¹ᵁ (V a ⊓ V b))
      (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map q ((Scheme.Modules.pullback i).obj M) (V a ⊓ V b)
        (ModuleSections.Construction.ModuleSectionsOver.map i π ρ hi M (U (r a) ⊓ U (r b)) (V a ⊓ V b)
          (ModuleCechD.Construction.ModuleCechPullback.cechPullback_overlap_preimage i U V r hr a b) (z (r a) (r b)))) =
    ModuleSections.Construction.ModuleSectionsOver.map j π' ρ' hj ((Scheme.Modules.pullback p).obj M)
      (p ⁻¹ᵁ (U (r a) ⊓ U (r b))) (q ⁻¹ᵁ (V a ⊓ V b))
      (ModuleCechD.Construction.ModuleCechPullback.cechPullback_overlap_preimage j (fun a => p ⁻¹ᵁ U a)
        (fun a => q ⁻¹ᵁ V a) r hr' a b)
      (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map p M (U (r a) ⊓ U (r b)) (z (r a) (r b)))
  rw [ModuleSections.Construction.ModuleSectionsOver.map_apply, ModuleSections.Construction.ModuleSectionsOver.map_apply]
  exact PullbackSectionCongr.Construction.PullbackSectionSquare.vertical i p q j h M (U (r a) ⊓ U (r b)) (V a ⊓ V b)
    (ModuleCechD.Construction.ModuleCechPullback.cechPullback_overlap_preimage i U V r hr a b)
    (ModuleCechD.Construction.ModuleCechPullback.cechPullback_overlap_preimage j (fun a => p ⁻¹ᵁ U a)
      (fun a => q ⁻¹ᵁ V a) r hr' a b) (z (r a) (r b))

end Construction.CechBaseChangeRestriction

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBaseMiddle
