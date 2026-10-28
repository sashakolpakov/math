import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductConstantTrivial
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CartesianFamily
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RationalFiber

/-! # Cartesian Product Trivial -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CartesianProductTrivial

noncomputable section

/-! Seesaw for Cartesian product families, with projectivity and integral
fibers supplied by the original factors and their affine section covers. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace Construction.CartesianProductSeesaw

variable {K : Type u} [Field K] [IsAlgClosed K] {A B X Y S : Scheme.{u}}
variable [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [ConnectedSpace S]
variable (a : A ⟶ Spec (.of K)) (b : B ⟶ Spec (.of K))
variable [IsProper a] [IsProper b] [GeometricallyIntegral a] [GeometricallyIntegral b]
variable (DA : AffineSectionOf.Construction.AffineSectionCover.Data A) (DB : AffineSectionOf.Construction.AffineSectionCover.Data B)
variable (f : X ⟶ S) (g : Y ⟶ S) (p : X ⟶ A) (q : Y ⟶ B) (t : S ⟶ Spec (.of K))
variable (hp : IsPullback p f a t) (hq : IsPullback q g b t)
variable {ι κ : Type u} [LinearOrder ι] [Fintype ι] [LinearOrder κ] [Fintype κ]
variable (U : ι → A.Opens) (V : κ → B.Opens)
variable (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
variable (hcU : iSup U = ⊤) (hcV : iSup V = ⊤)
variable (sX : S ⟶ X) (hsX : sX ≫ f = 𝟙 _) (sY : S ⟶ Y) (hsY : sY ≫ g = 𝟙 _)
variable (i₀ : ι) (hi₀ : ⊤ ≤ sX ⁻¹ᵁ (p ⁻¹ᵁ U i₀))
variable (j₀ : κ) (hj₀ : ⊤ ≤ sY ⁻¹ᵁ (q ⁻¹ᵁ V j₀))
variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (pullback f g))
variable (eX : (L.pullback (ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g sY hsY)).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
variable (eY : (L.pullback (ProductBaseAxes.Construction.ProductBaseChangeAxes.right f g sX hsX)).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)

include DA DB hp hq hU hV hcU hcV hi₀ hj₀ eX eY

theorem trivial (s : Spec (.of K) ⟶ S) (hs : s ≫ t = 𝟙 _)
    (he : (L.pullback (pullback.fst (pullback.fst f g ≫ f) s)).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (pullback (pullback.fst f g ≫ f) s)) :
    Nonempty (L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (pullback f g)) := by
  have : IsIntegral A := GeometricallyIntegral.isIntegral_of_subsingleton a
  have : IsIntegral B := GeometricallyIntegral.isIntegral_of_subsingleton b
  have : IsProper f := MorphismProperty.of_isPullback hp ‹IsProper a›
  have : IsProper g := MorphismProperty.of_isPullback hq ‹IsProper b›
  have : Flat f := MorphismProperty.of_isPullback hp (inferInstance : Flat a)
  have : Flat g := MorphismProperty.of_isPullback hq (inferInstance : Flat b)
  have : GeometricallyIntegral f := MorphismProperty.of_isPullback hp ‹GeometricallyIntegral a›
  have : GeometricallyIntegral g := MorphismProperty.of_isPullback hq ‹GeometricallyIntegral b›
  have : A.IsSeparated := CartesianFamily.Construction.CartesianFamilyProjective.separated a
  have : B.IsSeparated := CartesianFamily.Construction.CartesianFamilyProjective.separated b
  have : X.IsSeparated := CartesianFamily.Construction.CartesianFamilyProjective.separated f
  have : Y.IsSeparated := CartesianFamily.Construction.CartesianFamilyProjective.separated g
  have : (pullback f g).IsSeparated := CartesianFamily.Construction.CartesianFamilyProjective.separated (pullback.fst f g ≫ f)
  exact ProductConstantTrivial.Construction.ProductConstantSeesaw.trivial a b f g p q t hp hq
    (DA.projectivePresentation a) (DB.projectivePresentation b)
    (CartesianFamily.Construction.CartesianFamilyProjective.presentation a b f g p q t hp hq DA DB)
    U V hU hV hcU hcV sX hsX sY hsY i₀ hi₀ j₀ hj₀ L eX eY
    (RationalPoint.Construction.RationalPointResidue.point s)
    ⟨RationalFiber.Construction.RationalFiberTriviality.iso (pullback.fst f g ≫ f) t s hs L.sheaf he⟩

end Construction.CartesianProductSeesaw

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CartesianProductTrivial
