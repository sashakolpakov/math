import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductFiber
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductCech
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree

/-! # Geometric Product -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricProduct

noncomputable section

/-! Geometric product fibers supply the two-axis detector from ordinary
finite affine covers and a fiber trivialization. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.GeometricProductDetector

open OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductFamilyCover.Construction.ProductFamilyAxes OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes OAI.AlgebraicGeometry.Quotients.FiniteDescent.FamilyCechBaseChange.Construction.ProductFamilyCechBaseChange

variable {K : Type u} [Field K] {X Y S X' Y' : Scheme.{u}} [IsAffine S]
variable [X.IsSeparated] [Y.IsSeparated]
variable (f : X ⟶ S) (g : Y ⟶ S) [(pullback f g).IsSeparated]
variable (f' : X' ⟶ Spec (.of K)) (g' : Y' ⟶ Spec (.of K))
variable (p : X' ⟶ X) (q : Y' ⟶ Y) (t : Spec (.of K) ⟶ S)
variable (hp : IsPullback p f' f t) (hq : IsPullback q g' g t)
variable {ι κ : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (U : ι → X.Opens) (V : κ → Y.Opens)
variable (hU : ∀ a, IsAffineOpen (U a)) (hV : ∀ a, IsAffineOpen (V a))
variable (hcU : iSup U = ⊤) (hcV : iSup V = ⊤)
variable (sX : S ⟶ X) (hsX : sX ≫ f = 𝟙 _) (sY : S ⟶ Y) (hsY : sY ≫ g = 𝟙 _)
variable (i₀ : ι) (hi₀ : ⊤ ≤ sX ⁻¹ᵁ U i₀) (j₀ : κ) (hj₀ : ⊤ ≤ sY ⁻¹ᵁ V j₀)
variable [IsIntegral X'] [IsIntegral Y'] [UniversallyClosed f'] [UniversallyClosed g']
variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (pullback f g))

include hU hV hcU hcV hp hq

theorem jointly
    (he : (Scheme.Modules.pullback (pullback.fst (pullback.fst f g ≫ f) t)).obj L.sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (pullback (pullback.fst f g ≫ f) t)) :
    CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      ((ModuleCat.extendScalars t.appTop.hom).mapShortComplex.map
        (ProductFamilyCover.Construction.ProductFamilyAxes.left f g U V L.sheaf sY hsY j₀ hj₀))
      ((ModuleCat.extendScalars t.appTop.hom).mapShortComplex.map
        (ProductFamilyCover.Construction.ProductFamilyAxes.right f g U V L.sheaf sX hsX i₀ hi₀)) := by
  have : L.sheaf.IsQuasicoherent := LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  have : ((Scheme.Modules.pullback (ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g sY hsY)).obj L.sheaf).IsQuasicoherent :=
    LineBundleFree.Construction.LineBundleCoherence.quasicoherent (L.pullback (ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g sY hsY))
  have : ((Scheme.Modules.pullback (ProductBaseAxes.Construction.ProductBaseChangeAxes.right f g sX hsX)).obj L.sheaf).IsQuasicoherent :=
    LineBundleFree.Construction.LineBundleCoherence.quasicoherent (L.pullback (ProductBaseAxes.Construction.ProductBaseChangeAxes.right f g sX hsX))
  have : MorphismProperty.IsStableUnderBaseChange (@IsAffineHom : MorphismProperty Scheme.{u}) :=
    isAffineHom_isStableUnderBaseChange
  have : IsAffineHom t := inferInstance
  have : IsAffineHom p := MorphismProperty.of_isPullback hp.flip ‹IsAffineHom t›
  have : IsAffineHom q := MorphismProperty.of_isPullback hq.flip ‹IsAffineHom t›
  have hW := ProductCech.Construction.ProductCechCoverProperties.affine f g U V hU hV
  apply FamilyCechBaseChange.Construction.ProductFamilyCechBaseChange.jointly f g f' g' p q t hp hq U V
    sX hsX sY hsY i₀ hi₀ j₀ hj₀ L.sheaf hW
    (fun a b => (hW a).inf (hW b)) (fun a b c => ((hW a).inf (hW b)).inf (hW c))
    hU (fun a b => (hU a).inf (hU b)) (fun a b c => ((hU a).inf (hU b)).inf (hU c))
    hV (fun a b => (hV a).inf (hV b)) (fun a b c => ((hV a).inf (hV b)).inf (hV c))
  exact ProductFiber.Construction.ProductFiberAxisDetection.jointly f g f' g' p q t hp hq U V
    sX hsX sY hsY i₀ hi₀ j₀ hj₀ L.sheaf
    (fun a => (hU a).preimage p) (fun a => (hV a).preimage q)
    (fun a b => ((hU a).inf (hU b)).preimage p)
    (fun a b => ((hV a).inf (hV b)).preimage q)
    (ProductCech.Construction.ProductCechCoverProperties.preimage_covers U p hcU)
    (ProductCech.Construction.ProductCechCoverProperties.preimage_covers V q hcV)
    (CartesianBundle.Construction.CartesianBundleTriviality.iso (FamilyCechBaseChange.Construction.ProductFamilyCechBaseChange.baseMap f g f' g' p q t hp hq)
      (pullback.fst f g ≫ f) (pullback.fst f' g' ≫ f') t
      (ProductBaseLift.Construction.ProductBaseChangeSquare.isPullback f g f' g' p q t hp hq) L.sheaf he)

end Construction.GeometricProductDetector

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricProduct
