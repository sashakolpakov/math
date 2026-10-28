import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductOpenTriviality
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineTrivialityPropagation
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CartesianProductIs

/-! # Constant Product Cube -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductCube.Construction

noncomputable section

/-! Global cube triviality for two constant projective factors over an integral base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes

variable {K : Type} [Field K] [IsAlgClosed K]
variable {A B X Y S : Scheme} [IsIntegral S] [IsLocallyNoetherian S]
variable [IsIntegral A] [IsIntegral B] [A.IsSeparated] [B.IsSeparated]
variable [X.IsSeparated] [Y.IsSeparated]
variable (a : A ⟶ Spec (.of K)) (b : B ⟶ Spec (.of K)) [IsProper a] [IsProper b]
variable (f : X ⟶ S) (g : Y ⟶ S) [IsProper f] [IsProper g] [Flat f] [Flat g]
variable [GeometricallyIntegral f] [GeometricallyIntegral g]
variable (p : X ⟶ A) (q : Y ⟶ B) (t : S ⟶ Spec (.of K))
variable (hp : IsPullback p f a t) (hq : IsPullback q g b t)
variable (DA : AlgebraicGeometry.Quotients.FiniteDescent.AffineSectionOf.Construction.AffineSectionCover.Data A) (DB : AlgebraicGeometry.Quotients.FiniteDescent.AffineSectionOf.Construction.AffineSectionCover.Data B)
variable (sX : S ⟶ X) (hsX : sX ≫ f = 𝟙 _) (sY : S ⟶ Y) (hsY : sY ≫ g = 𝟙 _)
variable (i₀ : DA.I) (hi₀ : ⊤ ≤ sX ⁻¹ᵁ (p ⁻¹ᵁ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (DA.sectionHom i₀)))
variable (j₀ : DB.I) (hj₀ : ⊤ ≤ sY ⁻¹ᵁ (q ⁻¹ᵁ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (DB.sectionHom j₀)))
variable (L : (pullback f g).Modules) (hL : LineBundle.Construction.IsLineBundle L)
variable (eX : (Scheme.Modules.pullback (AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g sY hsY)).obj L ≅ LineBundle.Construction.structureSheafModule X)
variable (eY : (Scheme.Modules.pullback (AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.right f g sX hsX)).obj L ≅ LineBundle.Construction.structureSheafModule Y)

include hp hq DA DB hi₀ hj₀ hL eX eY in
omit [X.IsSeparated] [Y.IsSeparated] in
theorem constantProduct_lineBundle_trivial (x₀ : S)
    (he : Nonempty ((Scheme.Modules.pullback ((pullback.fst f g ≫ f).fiberι x₀)).obj L ≅
      LineBundle.Construction.structureSheafModule ((pullback.fst f g ≫ f).fiber x₀))) :
    Nonempty (L ≅ LineBundle.Construction.structureSheafModule (pullback f g)) := by
  let π := pullback.fst f g ≫ f
  let s := sX ≫ AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g sY hsY
  have hs : s ≫ π = 𝟙 S := by
    rw [Category.assoc, AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.left_over, hsX]
  let e := FiberTrivialityBaseChange.Construction.pullbackTrivialization_comp (AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g sY hsY) sX L eX
  apply AffineTrivialityPropagation.Construction.lineBundle_trivial_of_affine_fiber_propagation π s hs
    (AlgebraicGeometry.Quotients.FiniteDescent.CartesianProductIs.Construction.CartesianProductFunctions.product_app a p f t hp b q g hq) L hL e _ x₀ he
  intro U hU hstart
  obtain ⟨x, hx, he⟩ := hstart
  exact ConstantProductOpenTriviality.Construction.constantProduct_trivial_over_affineOpen a b f g p q t hp hq DA DB
    sX hsX sY hsY i₀ hi₀ j₀ hj₀ L hL eX eY U hU x hx he

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductCube.Construction
