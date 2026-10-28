import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.MorphismOver
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HomotopyBoundaryDetection
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricProduct
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RingEquiv
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.CoefficientUnitExactness

/-! # Cech Morphism Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.CechMorphismDetection

noncomputable section

/-! The geometric product detector applies to the actual full cochain
maps, including specialization to a prescribed coefficient field. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace ProductCechMorphismDetection

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
variable {ι κ : Type u} (U : ι → X.Opens) (V : κ → Y.Opens)
variable (M : (pullback f g).Modules)
variable (sX : S ⟶ X) (hsX : sX ≫ f = 𝟙 _) (sY : S ⟶ Y) (hsY : sY ≫ g = 𝟙 _)
variable (i₀ : ι) (hi₀ : ⊤ ≤ sX ⁻¹ᵁ U i₀) (j₀ : κ) (hj₀ : ⊤ ≤ sY ⁻¹ᵁ V j₀)

def left := Cech.MorphismOver.CechMorphismOver.map (Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g sY hsY)
  (pullback.fst f g ≫ f) f (Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.left_over f g sY hsY) M
  (Quotients.FiniteDescent.ProductFamilyCover.Construction.ProductFamilyAxes.cover f g U V) U (fun i => ⟨i, j₀⟩)
  (fun i => Quotients.FiniteDescent.ProductBaseOpens.Construction.ProductBaseChangeOpens.left f g sY hsY (U i) (V j₀) hj₀)

def right := Cech.MorphismOver.CechMorphismOver.map (Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.right f g sX hsX)
  (pullback.fst f g ≫ f) g (Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.right_over f g sX hsX) M
  (Quotients.FiniteDescent.ProductFamilyCover.Construction.ProductFamilyAxes.cover f g U V) V (fun j => ⟨i₀, j⟩)
  (fun j => Quotients.FiniteDescent.ProductBaseOpens.Construction.ProductBaseChangeOpens.right f g sX hsX (U i₀) (V j) hi₀)

theorem jointly_of_coordinates {K : Type u} [CommRing K] (a : Γ(S, ⊤) →+* K)
    (hd : Quotients.FiniteDescent.CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      ((ModuleCat.extendScalars a).mapShortComplex.map
        (Quotients.FiniteDescent.ProductFamilyCover.Construction.ProductFamilyAxes.left f g U V M sY hsY j₀ hj₀))
      ((ModuleCat.extendScalars a).mapShortComplex.map
        (Quotients.FiniteDescent.ProductFamilyCover.Construction.ProductFamilyAxes.right f g U V M sX hsX i₀ hi₀))) :
    Quotients.FiniteDescent.CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      ((ModuleCat.extendScalars a).mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} Γ(S, ⊤)) (ComplexShape.up ℕ) 0 1 2).map
          (left f g U V M sY hsY j₀ hj₀)))
      ((ModuleCat.extendScalars a).mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} Γ(S, ⊤)) (ComplexShape.up ℕ) 0 1 2).map
          (right f g U V M sX hsX i₀ hi₀))) := by
  apply HomotopyBoundaryDetection.CechBoundaryTransport.jointly_of_iso_middle_map
    (ModuleCat.extendScalars a) _ _ _ _
    (Quotients.FiniteDescent.CechShort.Construction.CechShortCoordinates.iso (pullback.fst f g ≫ f) M (Quotients.FiniteDescent.ProductFamilyCover.Construction.ProductFamilyAxes.cover f g U V))
    (Quotients.FiniteDescent.CechShort.Construction.CechShortCoordinates.iso f
      ((Scheme.Modules.pullback (Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g sY hsY)).obj M) U).hom
    (Quotients.FiniteDescent.CechShort.Construction.CechShortCoordinates.iso g
      ((Scheme.Modules.pullback (Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.right f g sX hsX)).obj M) V).hom _ _ hd
  · exact Cech.MorphismOver.CechMorphismOver.short_middle _ _ _ _ _ _ _ _ _
  · exact Cech.MorphismOver.CechMorphismOver.short_middle _ _ _ _ _ _ _ _ _

variable [IsAffine S] [X.IsSeparated] [Y.IsSeparated] [(pullback f g).IsSeparated]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (hU : ∀ a, IsAffineOpen (U a)) (hV : ∀ a, IsAffineOpen (V a))
variable (hcU : iSup U = ⊤) (hcV : iSup V = ⊤)
variable (K : Type u) [Field K] [Algebra Γ(S, ⊤) K]
variable [IsIntegral (pullback f (ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldPoint S K))]
variable [IsIntegral (pullback g (ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldPoint S K))]
variable [UniversallyClosed f] [UniversallyClosed g]

include hU hV hcU hcV

theorem coefficient_jointly (L : Line.Bundles.LineBundle (pullback f g))
    (he : (L.pullback (pullback.fst (pullback.fst f g ≫ f)
      (ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldPoint S K))).sheaf ≅
        Line.Bundles.structureModule (pullback (pullback.fst f g ≫ f) (ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldPoint S K))) :
    Quotients.FiniteDescent.CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      ((ModuleCat.extendScalars (algebraMap Γ(S, ⊤) K)).mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} Γ(S, ⊤)) (ComplexShape.up ℕ) 0 1 2).map
          (left f g U V L.sheaf sY hsY j₀ hj₀)))
      ((ModuleCat.extendScalars (algebraMap Γ(S, ⊤) K)).mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} Γ(S, ⊤)) (ComplexShape.up ℕ) 0 1 2).map
          (right f g U V L.sheaf sX hsX i₀ hi₀))) := by
  let q := ReferenceFamily.Affine.CoefficientUnitExactness.coefficientFieldPoint S K
  have hd := Quotients.FiniteDescent.GeometricProduct.Construction.GeometricProductDetector.jointly f g (pullback.snd f q) (pullback.snd g q)
    (pullback.fst f q) (pullback.fst g q) q
    (IsPullback.of_hasPullback f q) (IsPullback.of_hasPullback g q)
    U V hU hV hcU hcV sX hsX sY hsY i₀ hi₀ j₀ hj₀ L he
  have ht := Quotients.FiniteDescent.RingEquiv.Construction.RingEquivCechDetection.composite (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
    q.appTop.hom _ _ hd
  have heq : (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toRingHom.comp q.appTop.hom =
      algebraMap Γ(S, ⊤) K :=
    ReferenceFamily.Affine.CoefficientPoints.affineCoefficientPoint_coefficients S (algebraMap Γ(S, ⊤) K)
  rw [heq] at ht
  exact jointly_of_coordinates f g U V L.sheaf sX hsX sY hsY i₀ hi₀ j₀ hj₀ _ ht

end ProductCechMorphismDetection

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.CechMorphismDetection
