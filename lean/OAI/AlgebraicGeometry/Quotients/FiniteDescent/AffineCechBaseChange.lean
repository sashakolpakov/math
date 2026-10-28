import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrdinaryAffineTwo
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrdinaryCechOne
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ScalarShort

/-! # Affine Cech Base Change -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineCechBaseChange

noncomputable section

/-! Canonical base change of the actual ordinary affine-cover Cech short
complex, as an isomorphism with specified values on pure tensors. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped ChangeOfRings

universe u

namespace Construction.OrdinaryAffineCechBaseChange

variable {X Y S T : Scheme.{u}} [IsAffine S] [IsAffine T]
variable (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
variable (h : IsPullback f ρ π g) (M : X.Modules) [M.IsQuasicoherent]
variable {ι : Type u} [Finite ι] (U : ι → X.Opens)
variable (hU : ∀ i, IsAffineOpen (U i))
variable (hUU : ∀ i j, IsAffineOpen (U i ⊓ U j))
variable (hUUU : ∀ i j k, IsAffineOpen ((U i ⊓ U j) ⊓ U k))

def iso : (CechShort.Construction.CechShortCoordinates.target π M U).map (ModuleCat.extendScalars g.appTop.hom) ≅
    CechShort.Construction.CechShortCoordinates.target ρ ((Scheme.Modules.pullback f).obj M) (fun i => f ⁻¹ᵁ U i) :=
  ScalarShort.Construction.ScalarShortComplexData.iso g.appTop.hom _ _
    (OrdinaryCechOne.Construction.OrdinaryCechPullbackValues.zero f π ρ M U) (OrdinaryCechOne.Construction.OrdinaryCechPullbackValues.one f π ρ M U)
    (OrdinaryCechOne.Construction.OrdinaryCechPullbackValues.two f π ρ M U)
    (OrdinaryAffineTwo.Construction.OrdinaryAffineCechTerms.zeroData f π ρ g h M U hU)
    (OrdinaryAffineTwo.Construction.OrdinaryAffineCechTerms.oneData f π ρ g h M U hUU)
    (OrdinaryAffineTwo.Construction.OrdinaryAffineCechTerms.twoData f π ρ g h M U hUUU)
    (fun z => (OrdinaryCechOne.Construction.OrdinaryCechPullbackValues.differential_zero f π ρ M U z).symm)
    (fun z => (OrdinaryCechOne.Construction.OrdinaryCechPullbackValues.differential_one f π ρ M U z).symm)

theorem middle_one (z : (CechShort.Construction.CechShortCoordinates.target π M U).X₂) :
    (iso f π ρ g h M U hU hUU hUUU).hom.τ₂ ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] z) =
      OrdinaryCechOne.Construction.OrdinaryCechPullbackValues.one f π ρ M U z :=
  (OrdinaryAffineTwo.Construction.OrdinaryAffineCechTerms.oneData f π ρ g h M U hUU).property z

theorem first_one (z : (CechShort.Construction.CechShortCoordinates.target π M U).X₁) :
    (iso f π ρ g h M U hU hUU hUUU).hom.τ₁ ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] z) =
      OrdinaryCechOne.Construction.OrdinaryCechPullbackValues.zero f π ρ M U z :=
  (OrdinaryAffineTwo.Construction.OrdinaryAffineCechTerms.zeroData f π ρ g h M U hU).property z

end Construction.OrdinaryAffineCechBaseChange

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineCechBaseChange
