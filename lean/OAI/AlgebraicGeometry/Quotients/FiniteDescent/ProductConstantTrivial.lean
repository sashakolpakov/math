import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductConstantIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Seesaw
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CartesianProductIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductIntegral

/-! # Product Constant Trivial -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductConstantTrivial

noncomputable section

/-! Seesaw for a product of two constant projective integral families over
a connected affine base: two trivial axes and one trivial fiber force
triviality of the whole line bundle. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace Construction.ProductConstantSeesaw

variable {K : Type u} [Field K] [IsAlgClosed K] {A B X Y S : Scheme.{u}}
variable [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
variable [A.IsSeparated] [B.IsSeparated] [X.IsSeparated] [Y.IsSeparated]
variable (a : A ⟶ Spec (.of K)) (b : B ⟶ Spec (.of K))
variable [IsIntegral A] [IsIntegral B] [IsProper a] [IsProper b] [ConnectedSpace S]
variable (f : X ⟶ S) (g : Y ⟶ S) [(pullback f g).IsSeparated]
variable [IsProper f] [IsProper g] [Flat f] [Flat g]
variable [GeometricallyIntegral f] [GeometricallyIntegral g]
variable (p : X ⟶ A) (q : Y ⟶ B) (t : S ⟶ Spec (.of K))
variable (hp : IsPullback p f a t) (hq : IsPullback q g b t)
variable (PA : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk a))
variable (PB : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk b))
variable (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk (pullback.fst f g ≫ f)))
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

include hp hq PA PB P hU hV hcU hcV hi₀ hj₀ eX eY

theorem trivial (x₀ : S)
    (he : Nonempty ((L.pullback ((pullback.fst f g ≫ f).fiberι x₀)).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((pullback.fst f g ≫ f).fiber x₀))) :
    Nonempty (L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (pullback f g)) := by
  have hI := ProductIntegral.Construction.ProductIntegralFibers.integral f g
  have hall := ProductConstantIs.Construction.ProductConstantTrivialityLocus.all_fibers a b f g p q t hp hq PA PB P
    U V hU hV hcU hcV sX hsX sY hsY i₀ hi₀ j₀ hj₀ L eX eY hI x₀ he
  have hn (x : S) : ∃ W : S.Opens, x ∈ W ∧ Nonempty
      ((L.pullback ((pullback.fst f g ≫ f) ⁻¹ᵁ W).ι).sheaf ≅
        AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((pullback.fst f g ≫ f) ⁻¹ᵁ W).toScheme) := by
    have := hI x
    exact ProductConstantOpen.Construction.ProductConstantFrameNeighborhood.exists_open a b f g p q t hp hq PA PB P
      U V hU hV hcU hcV sX hsX sY hsY i₀ hi₀ j₀ hj₀ L eX eY x (hall x)
  let r := sX ≫ ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g sY hsY
  have hr : r ≫ (pullback.fst f g ≫ f) = 𝟙 S := by
    rw [Category.assoc, ProductBaseAxes.Construction.ProductBaseChangeAxes.left_over, hsX]
  let er : (Scheme.Modules.pullback r).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S :=
    ((Scheme.Modules.pullbackComp sX (ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g sY hsY)).app L.sheaf).symm ≪≫
      (Scheme.Modules.pullback sX).mapIso eX ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso sX
  exact ⟨Seesaw.Construction.SeesawDescent.trivial (pullback.fst f g ≫ f) L.sheaf
    (CartesianProductIs.Construction.CartesianProductFunctions.product_restricted_unit a p f t hp b q g hq) hn r hr er⟩

end Construction.ProductConstantSeesaw

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductConstantTrivial
