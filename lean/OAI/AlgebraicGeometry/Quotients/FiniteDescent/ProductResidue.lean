import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricProduct
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FiberCech
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # Product Residue -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductResidue

noncomputable section

/-! Two product axes detect Cech cohomology after evaluation in the actual
residue field, including arbitrary coefficient trivializations on the axes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.ProductResidueDetector

variable {X Y S : Scheme.{u}} [IsAffine S] [X.IsSeparated] [Y.IsSeparated]
variable (f : X ⟶ S) (g : Y ⟶ S) [(pullback f g).IsSeparated]
variable [IsProper f] [IsProper g] [GeometricallyIntegral f] [GeometricallyIntegral g]
variable {ι κ : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (U : ι → X.Opens) (V : κ → Y.Opens)
variable (hU : ∀ a, IsAffineOpen (U a)) (hV : ∀ a, IsAffineOpen (V a))
variable (hcU : iSup U = ⊤) (hcV : iSup V = ⊤)
variable (sX : S ⟶ X) (hsX : sX ≫ f = 𝟙 _) (sY : S ⟶ Y) (hsY : sY ≫ g = 𝟙 _)
variable (i₀ : ι) (hi₀ : ⊤ ≤ sX ⁻¹ᵁ U i₀) (j₀ : κ) (hj₀ : ⊤ ≤ sY ⁻¹ᵁ V j₀)
variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (pullback f g)) (x : S)
variable (he : Nonempty ((L.pullback ((pullback.fst f g ≫ f).fiberι x)).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((pullback.fst f g ≫ f).fiber x)))

include hU hV hcU hcV he

theorem jointly :
    CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      ((ModuleCat.extendScalars (S.Γevaluation x).hom).mapShortComplex.map
        (ProductFamilyCover.Construction.ProductFamilyAxes.left f g U V L.sheaf sY hsY j₀ hj₀))
      ((ModuleCat.extendScalars (S.Γevaluation x).hom).mapShortComplex.map
        (ProductFamilyCover.Construction.ProductFamilyAxes.right f g U V L.sheaf sX hsX i₀ hi₀)) := by
  have : IsProper (f.fiberToSpecResidueField x) :=
    inferInstanceAs (IsProper (pullback.snd f (S.fromSpecResidueField x)))
  have : IsProper (g.fiberToSpecResidueField x) :=
    inferInstanceAs (IsProper (pullback.snd g (S.fromSpecResidueField x)))
  apply FiberCech.Construction.FiberCechDetection.from_spectrum S x
  exact GeometricProduct.Construction.GeometricProductDetector.jointly f g (f.fiberToSpecResidueField x)
    (g.fiberToSpecResidueField x) (f.fiberι x) (g.fiberι x) (S.fromSpecResidueField x)
    (IsPullback.of_hasPullback f (S.fromSpecResidueField x))
    (IsPullback.of_hasPullback g (S.fromSpecResidueField x)) U V hU hV hcU hcV
    sX hsX sY hsY i₀ hi₀ j₀ hj₀ L he.some

theorem normalized (N₁ : X.Modules) (N₂ : Y.Modules)
    (e₁ : (Scheme.Modules.pullback (ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g sY hsY)).obj L.sheaf ≅ N₁)
    (e₂ : (Scheme.Modules.pullback (ProductBaseAxes.Construction.ProductBaseChangeAxes.right f g sX hsX)).obj L.sheaf ≅ N₂) :
    CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      ((ModuleCat.extendScalars (S.Γevaluation x).hom).mapShortComplex.map
        (ProductFamilyCover.Construction.ProductFamilyAxes.left f g U V L.sheaf sY hsY j₀ hj₀ ≫
          ((CechCoefficient.Construction.CechCoefficientFunctor.moduleFunctor f U).mapIso e₁).hom))
      ((ModuleCat.extendScalars (S.Γevaluation x).hom).mapShortComplex.map
        (ProductFamilyCover.Construction.ProductFamilyAxes.right f g U V L.sheaf sX hsX i₀ hi₀ ≫
          ((CechCoefficient.Construction.CechCoefficientFunctor.moduleFunctor g V).mapIso e₂).hom)) := by
  rw [Functor.map_comp, Functor.map_comp]
  exact CechBoundary.Construction.CechBoundaryTransport.jointly_postcompose_isos _ _
    ((ModuleCat.extendScalars (S.Γevaluation x).hom).mapShortComplex.mapIso
      ((CechCoefficient.Construction.CechCoefficientFunctor.moduleFunctor f U).mapIso e₁))
    ((ModuleCat.extendScalars (S.Γevaluation x).hom).mapShortComplex.mapIso
      ((CechCoefficient.Construction.CechCoefficientFunctor.moduleFunctor g V).mapIso e₂))
    (jointly f g U V hU hV hcU hcV sX hsX sY hsY i₀ hi₀ j₀ hj₀ L x he)

end Construction.ProductResidueDetector

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductResidue
