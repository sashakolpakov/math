import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenCartesian

/-! # Affine Neighborhood Trivial -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineNeighborhoodTrivial.Construction.AffineNeighborhoodSeesaw

noncomputable section

/-! Product seesaw over an integral base whose points share affine
neighborhoods with the chosen rational origin. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {A B X Y S : Scheme.{u}}
variable [IsIntegral S] [IsLocallyNoetherian S]
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
variable (s : Spec (.of K) ⟶ S) (hs : s ≫ t = 𝟙 _)
variable (he : (L.pullback (pullback.fst (pullback.fst f g ≫ f) s)).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (pullback (pullback.fst f g ≫ f) s))

variable (hN : ∀ x : S, ∃ W : S.Opens, IsAffineOpen W ∧ x ∈ W ∧ RationalPoint.Construction.RationalPointResidue.point s ∈ W)

include DA DB hp hq hU hV hcU hcV hi₀ hj₀ eX eY hs he hN

theorem trivial : Nonempty (L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (pullback f g)) := by
  have : IsIntegral A := GeometricallyIntegral.isIntegral_of_subsingleton a
  have : IsIntegral B := GeometricallyIntegral.isIntegral_of_subsingleton b
  have hn (x : S) : ∃ W : S.Opens, x ∈ W ∧ Nonempty
      ((L.pullback ((pullback.fst f g ≫ f) ⁻¹ᵁ W).ι).sheaf ≅
        AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((pullback.fst f g ≫ f) ⁻¹ᵁ W).toScheme) := by
    obtain ⟨W, hW, hx, hsW⟩ := hN x
    exact ⟨W, hx, OpenCartesian.Construction.OpenCartesianProductSeesaw.frame a b DA DB f g p q t hp hq
      U V hU hV hcU hcV sX hsX sY hsY i₀ hi₀ j₀ hj₀ L eX eY s hs he W hW hsW⟩
  let r := sX ≫ ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g sY hsY
  have hr : r ≫ (pullback.fst f g ≫ f) = 𝟙 S := by
    rw [Category.assoc, ProductBaseAxes.Construction.ProductBaseChangeAxes.left_over, hsX]
  let er : (Scheme.Modules.pullback r).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S :=
    ((Scheme.Modules.pullbackComp sX (ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g sY hsY)).app L.sheaf).symm ≪≫
      (Scheme.Modules.pullback sX).mapIso eX ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso sX
  exact ⟨Seesaw.Construction.SeesawDescent.trivial (pullback.fst f g ≫ f) L.sheaf
    (CartesianProductIs.Construction.CartesianProductFunctions.product_restricted_unit a p f t hp b q g hq) hn r hr er⟩

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineNeighborhoodTrivial.Construction.AffineNeighborhoodSeesaw
