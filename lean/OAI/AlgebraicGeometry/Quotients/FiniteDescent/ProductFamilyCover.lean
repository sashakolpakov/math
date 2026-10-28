import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseOpens
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TrivialProduct
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechShort

/-! # Product Family Cover -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductFamilyCover

noncomputable section

/-! The two geometric axis maps on ordinary Cech complexes of a product
family, over an arbitrary base. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace Construction.ProductFamilyAxes

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
variable {ι κ : Type u} (U : ι → X.Opens) (V : κ → Y.Opens)

abbrev cover (a : Σ _ : ι, κ) : (pullback f g).Opens :=
  pullback.fst f g ⁻¹ᵁ U a.1 ⊓ pullback.snd f g ⁻¹ᵁ V a.2

variable (M : (pullback f g).Modules)

abbrev source := CechShort.Construction.CechShortCoordinates.target (pullback.fst f g ≫ f) M (cover f g U V)

def left (s : S ⟶ Y) (hs : s ≫ g = 𝟙 _) (j : κ) (hj : ⊤ ≤ s ⁻¹ᵁ V j) :=
  ModuleCechPullbackShort.Construction.ModuleCechPullback.shortMap (ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g s hs) (pullback.fst f g ≫ f) f
    (ProductBaseAxes.Construction.ProductBaseChangeAxes.left_over f g s hs) M (cover f g U V) U (fun i => ⟨i, j⟩)
    (fun i => ProductBaseOpens.Construction.ProductBaseChangeOpens.left f g s hs (U i) (V j) hj)

def right (s : S ⟶ X) (hs : s ≫ f = 𝟙 _) (i : ι) (hi : ⊤ ≤ s ⁻¹ᵁ U i) :=
  ModuleCechPullbackShort.Construction.ModuleCechPullback.shortMap (ProductBaseAxes.Construction.ProductBaseChangeAxes.right f g s hs) (pullback.fst f g ≫ f) g
    (ProductBaseAxes.Construction.ProductBaseChangeAxes.right_over f g s hs) M (cover f g U V) V (fun j => ⟨i, j⟩)
    (fun j => ProductBaseOpens.Construction.ProductBaseChangeOpens.right f g s hs (U i) (V j) hi)

end Construction.ProductFamilyAxes

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductFamilyCover
