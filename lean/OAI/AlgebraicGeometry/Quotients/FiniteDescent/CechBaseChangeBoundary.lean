import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBaseMiddle
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBoundary

/-! # Cech Base Change Boundary -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBaseChangeBoundary

noncomputable section

/-! An axis boundary after scalar extension is a boundary on the actual
Cartesian fiber, through the canonical Cech comparison. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

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

include hi hj h hp hq hr hr' hU hUU hUUU hV hVV hVVV

theorem boundary
    (z : ((ModuleCat.extendScalars g.appTop.hom).mapShortComplex.obj
      (CechShort.Construction.CechShortCoordinates.target π M U)).X₂)
    (hz : ((ModuleCat.extendScalars g.appTop.hom).map
      (ModuleCechPullbackShort.Construction.ModuleCechPullback.shortMap i π ρ hi M U V r hr).τ₂) z ∈
        ((ModuleCat.extendScalars g.appTop.hom).mapShortComplex.obj
          (CechShort.Construction.CechShortCoordinates.target ρ ((Scheme.Modules.pullback i).obj M) V)).f.hom.range) :
    (ModuleCechPullbackShort.Construction.ModuleCechPullback.shortMap j π' ρ' hj ((Scheme.Modules.pullback p).obj M)
      (fun a => p ⁻¹ᵁ U a) (fun a => q ⁻¹ᵁ V a) r hr').τ₂
        ((CechBaseMiddle.Construction.CechBaseChangeRestriction.sourceIso p π π' g hp M U hU hUU hUUU).hom.τ₂ z) ∈
      (CechShort.Construction.CechShortCoordinates.target ρ' ((Scheme.Modules.pullback j).obj
        ((Scheme.Modules.pullback p).obj M)) (fun a => q ⁻¹ᵁ V a)).f.hom.range := by
  have hb := CechBoundary.Construction.CechBoundaryTransport.boundary
    ((CechBaseMiddle.Construction.CechBaseChangeRestriction.targetIso i q ρ ρ' g hq M V hV hVV hVVV).hom ≫
      (CechBaseMiddle.Construction.CechBaseChangeRestriction.coefficientIso i p q j ρ' h M V).hom)
    (((ModuleCat.extendScalars g.appTop.hom).map
      (ModuleCechPullbackShort.Construction.ModuleCechPullback.shortMap i π ρ hi M U V r hr).τ₂) z) hz
  have he := ConcreteCategory.congr_hom
    (CechBaseMiddle.Construction.CechBaseChangeRestriction.middle i p q j π ρ π' ρ' g hi hj h hp hq M U V r hr hr'
      hU hUU hUUU hV hVV hVVV) z
  exact he ▸ hb

end Construction.CechBaseChangeRestriction

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBaseChangeBoundary
