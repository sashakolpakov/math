import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductFamilyCover
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBaseChangeBoundary

/-! # Family Cech Base Change -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.FamilyCechBaseChange

noncomputable section

/-! Base change of the two actual product-family axes detects boundaries
whenever the axes on the Cartesian fiber do. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.ProductFamilyCechBaseChange

open OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductFamilyCover.Construction.ProductFamilyAxes OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes

variable {X Y S X' Y' T : Scheme.{u}} [IsAffine S] [IsAffine T]
variable (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ T) (g' : Y' ⟶ T)
variable (p : X' ⟶ X) (q : Y' ⟶ Y) (t : T ⟶ S)
variable (hp : IsPullback p f' f t) (hq : IsPullback q g' g t)
variable {ι κ : Type u} [Finite ι] [Finite κ] (U : ι → X.Opens) (V : κ → Y.Opens)
variable (sX : S ⟶ X) (hsX : sX ≫ f = 𝟙 _) (sY : S ⟶ Y) (hsY : sY ≫ g = 𝟙 _)
variable (i₀ : ι) (hi₀ : ⊤ ≤ sX ⁻¹ᵁ U i₀) (j₀ : κ) (hj₀ : ⊤ ≤ sY ⁻¹ᵁ V j₀)

abbrev baseMap := ProductBaseLift.Construction.ProductBaseChangeSquare.map f g f' g' p q t hp hq
abbrev pulledCover := fun a => baseMap f g f' g' p q t hp hq ⁻¹ᵁ ProductFamilyCover.Construction.ProductFamilyAxes.cover f g U V a

omit [IsAffine S] [IsAffine T] [Finite ι] [Finite κ] in
include hj₀ in
theorem left_refines (a : ι) :
    p ⁻¹ᵁ U a ≤ ProductBaseAxes.Construction.ProductBaseChangeAxes.liftedLeft g f' g' q t hq sY hsY ⁻¹ᵁ
      pulledCover f g f' g' p q t hp hq U V ⟨a, j₀⟩ := by
  change p ⁻¹ᵁ U a ≤ (ProductBaseAxes.Construction.ProductBaseChangeAxes.liftedLeft g f' g' q t hq sY hsY ≫
    baseMap f g f' g' p q t hp hq) ⁻¹ᵁ ProductFamilyCover.Construction.ProductFamilyAxes.cover f g U V ⟨a, j₀⟩
  rw [ProductBaseAxes.Construction.ProductBaseChangeAxes.left_square]
  exact fun x hx => ProductBaseOpens.Construction.ProductBaseChangeOpens.left f g sY hsY (U a) (V j₀) hj₀ hx

omit [IsAffine S] [IsAffine T] [Finite ι] [Finite κ] in
include hi₀ in
theorem right_refines (a : κ) :
    q ⁻¹ᵁ V a ≤ ProductBaseAxes.Construction.ProductBaseChangeAxes.liftedRight f f' g' p t hp sX hsX ⁻¹ᵁ
      pulledCover f g f' g' p q t hp hq U V ⟨i₀, a⟩ := by
  change q ⁻¹ᵁ V a ≤ (ProductBaseAxes.Construction.ProductBaseChangeAxes.liftedRight f f' g' p t hp sX hsX ≫
    baseMap f g f' g' p q t hp hq) ⁻¹ᵁ ProductFamilyCover.Construction.ProductFamilyAxes.cover f g U V ⟨i₀, a⟩
  rw [ProductBaseAxes.Construction.ProductBaseChangeAxes.right_square]
  exact fun x hx => ProductBaseOpens.Construction.ProductBaseChangeOpens.right f g sX hsX (U i₀) (V a) hi₀ hx

variable (M : (pullback f g).Modules) [M.IsQuasicoherent]
variable [((Scheme.Modules.pullback (ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g sY hsY)).obj M).IsQuasicoherent]
variable [((Scheme.Modules.pullback (ProductBaseAxes.Construction.ProductBaseChangeAxes.right f g sX hsX)).obj M).IsQuasicoherent]

def fiberLeft := ModuleCechPullbackShort.Construction.ModuleCechPullback.shortMap (ProductBaseAxes.Construction.ProductBaseChangeAxes.liftedLeft g f' g' q t hq sY hsY)
  (pullback.fst f' g' ≫ f') f' (ProductBaseAxes.Construction.ProductBaseChangeAxes.left_over f' g' _ _)
  ((Scheme.Modules.pullback (baseMap f g f' g' p q t hp hq)).obj M)
  (pulledCover f g f' g' p q t hp hq U V) (fun a => p ⁻¹ᵁ U a) (fun a => ⟨a, j₀⟩)
  (left_refines f g f' g' p q t hp hq U V sY hsY j₀ hj₀)

def fiberRight := ModuleCechPullbackShort.Construction.ModuleCechPullback.shortMap (ProductBaseAxes.Construction.ProductBaseChangeAxes.liftedRight f f' g' p t hp sX hsX)
  (pullback.fst f' g' ≫ f') g' (ProductBaseAxes.Construction.ProductBaseChangeAxes.right_over f' g' _ _)
  ((Scheme.Modules.pullback (baseMap f g f' g' p q t hp hq)).obj M)
  (pulledCover f g f' g' p q t hp hq U V) (fun a => q ⁻¹ᵁ V a) (fun a => ⟨i₀, a⟩)
  (right_refines f g f' g' p q t hp hq U V sX hsX i₀ hi₀)

variable (hW : ∀ a, IsAffineOpen (ProductFamilyCover.Construction.ProductFamilyAxes.cover f g U V a))
variable (hWW : ∀ a b, IsAffineOpen (ProductFamilyCover.Construction.ProductFamilyAxes.cover f g U V a ⊓ ProductFamilyCover.Construction.ProductFamilyAxes.cover f g U V b))
variable (hWWW : ∀ a b c, IsAffineOpen ((ProductFamilyCover.Construction.ProductFamilyAxes.cover f g U V a ⊓ ProductFamilyCover.Construction.ProductFamilyAxes.cover f g U V b) ⊓ ProductFamilyCover.Construction.ProductFamilyAxes.cover f g U V c))
variable (hU : ∀ a, IsAffineOpen (U a)) (hUU : ∀ a b, IsAffineOpen (U a ⊓ U b))
variable (hUUU : ∀ a b c, IsAffineOpen ((U a ⊓ U b) ⊓ U c))
variable (hV : ∀ a, IsAffineOpen (V a)) (hVV : ∀ a b, IsAffineOpen (V a ⊓ V b))
variable (hVVV : ∀ a b c, IsAffineOpen ((V a ⊓ V b) ⊓ V c))

include hW hWW hWWW hU hUU hUUU hV hVV hVVV

theorem jointly
    (hd : CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      (fiberLeft f g f' g' p q t hp hq U V sY hsY j₀ hj₀ M)
      (fiberRight f g f' g' p q t hp hq U V sX hsX i₀ hi₀ M)) :
    CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      ((ModuleCat.extendScalars t.appTop.hom).mapShortComplex.map
        (ProductFamilyCover.Construction.ProductFamilyAxes.left f g U V M sY hsY j₀ hj₀))
      ((ModuleCat.extendScalars t.appTop.hom).mapShortComplex.map
        (ProductFamilyCover.Construction.ProductFamilyAxes.right f g U V M sX hsX i₀ hi₀)) := by
  let e := AffineCechBaseChange.Construction.OrdinaryAffineCechBaseChange.iso (baseMap f g f' g' p q t hp hq)
    (pullback.fst f g ≫ f) (pullback.fst f' g' ≫ f') t
    (ProductBaseLift.Construction.ProductBaseChangeSquare.isPullback f g f' g' p q t hp hq) M (ProductFamilyCover.Construction.ProductFamilyAxes.cover f g U V) hW hWW hWWW
  intro z hz hb₁ hb₂
  apply CechBoundary.Construction.CechBoundaryTransport.reflect e z hz
  apply hd (e.hom.τ₂ z) (CechBoundary.Construction.CechBoundaryTransport.cycle e.hom z hz)
  · exact CechBaseChangeBoundary.Construction.CechBaseChangeRestriction.boundary
      (ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g sY hsY) (baseMap f g f' g' p q t hp hq) p
      (ProductBaseAxes.Construction.ProductBaseChangeAxes.liftedLeft g f' g' q t hq sY hsY)
      (pullback.fst f g ≫ f) f (pullback.fst f' g' ≫ f') f' t
      (ProductBaseAxes.Construction.ProductBaseChangeAxes.left_over f g sY hsY) (ProductBaseAxes.Construction.ProductBaseChangeAxes.left_over f' g' _ _)
      (ProductBaseAxes.Construction.ProductBaseChangeAxes.left_square f g f' g' p q t hp hq sY hsY).symm
      (ProductBaseLift.Construction.ProductBaseChangeSquare.isPullback f g f' g' p q t hp hq) hp M
      (ProductFamilyCover.Construction.ProductFamilyAxes.cover f g U V) U (fun a => ⟨a, j₀⟩)
      (fun a => ProductBaseOpens.Construction.ProductBaseChangeOpens.left f g sY hsY (U a) (V j₀) hj₀)
      (left_refines f g f' g' p q t hp hq U V sY hsY j₀ hj₀)
      hW hWW hWWW hU hUU hUUU z hb₁
  · exact CechBaseChangeBoundary.Construction.CechBaseChangeRestriction.boundary
      (ProductBaseAxes.Construction.ProductBaseChangeAxes.right f g sX hsX) (baseMap f g f' g' p q t hp hq) q
      (ProductBaseAxes.Construction.ProductBaseChangeAxes.liftedRight f f' g' p t hp sX hsX)
      (pullback.fst f g ≫ f) g (pullback.fst f' g' ≫ f') g' t
      (ProductBaseAxes.Construction.ProductBaseChangeAxes.right_over f g sX hsX) (ProductBaseAxes.Construction.ProductBaseChangeAxes.right_over f' g' _ _)
      (ProductBaseAxes.Construction.ProductBaseChangeAxes.right_square f g f' g' p q t hp hq sX hsX).symm
      (ProductBaseLift.Construction.ProductBaseChangeSquare.isPullback f g f' g' p q t hp hq) hq M
      (ProductFamilyCover.Construction.ProductFamilyAxes.cover f g U V) V (fun a => ⟨i₀, a⟩)
      (fun a => ProductBaseOpens.Construction.ProductBaseChangeOpens.right f g sX hsX (U i₀) (V a) hi₀)
      (right_refines f g f' g' p q t hp hq U V sX hsX i₀ hi₀)
      hW hWW hWWW hV hVV hVVV z hb₂

end Construction.ProductFamilyCechBaseChange

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.FamilyCechBaseChange
