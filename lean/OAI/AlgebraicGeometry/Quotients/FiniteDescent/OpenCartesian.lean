import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CartesianProductTrivial
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BaseChanged

/-! # Open Cartesian -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenCartesian

noncomputable section

/-! On every affine open of an integral base containing the chosen
rational point, product seesaw gives a frame for the whole inverse image. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace Construction.OpenCartesianProductSeesaw

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

include DA DB hp hq hU hV hcU hcV hi₀ hj₀ eX eY hs he

theorem frame (W : S.Opens) (hW : IsAffineOpen W) (hsW : RationalPoint.Construction.RationalPointResidue.point s ∈ W) :
    Nonempty ((L.pullback ((pullback.fst f g ≫ f) ⁻¹ᵁ W).ι).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((pullback.fst f g ≫ f) ⁻¹ᵁ W).toScheme) := by
  have : IsAffine W.toScheme := hW
  have : Nonempty W.toScheme := ⟨⟨RationalPoint.Construction.RationalPointResidue.point s, hsW⟩⟩
  have : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  have : IsLocallyNoetherian W.toScheme := isLocallyNoetherian_of_isOpenImmersion W.ι
  have : IsNoetherianRing Γ(W.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top W.toScheme⟩
  let f' := pullback.snd f W.ι
  let g' := pullback.snd g W.ι
  let p' := pullback.fst f W.ι
  let q' := pullback.fst g W.ι
  let hx := IsPullback.of_hasPullback f W.ι
  let hy := IsPullback.of_hasPullback g W.ι
  let m := ProductBaseLift.Construction.ProductBaseChangeSquare.map f g f' g' p' q' W.ι hx hy
  let hm := ProductBaseLift.Construction.ProductBaseChangeSquare.isPullback f g f' g' p' q' W.ι hx hy
  let L' := L.pullback m
  let sx := ProductBaseAxes.Construction.ProductBaseChangeAxes.baseSection f f' p' W.ι hx sX hsX
  let sy := ProductBaseAxes.Construction.ProductBaseChangeAxes.baseSection g g' q' W.ι hy sY hsY
  have hsx : sx ≫ f' = 𝟙 _ := ProductBaseAxes.Construction.ProductBaseChangeAxes.section_over f f' p' W.ι hx sX hsX
  have hsy : sy ≫ g' = 𝟙 _ := ProductBaseAxes.Construction.ProductBaseChangeAxes.section_over g g' q' W.ι hy sY hsY
  have hix : ⊤ ≤ sx ⁻¹ᵁ ((p' ≫ p) ⁻¹ᵁ U i₀) := by
    change ⊤ ≤ ((sx ≫ p') ≫ p) ⁻¹ᵁ U i₀
    rw [show sx ≫ p' = W.ι ≫ sX from hx.lift_fst _ _ _]
    exact fun x _ => hi₀ (show W.ι x ∈ (⊤ : S.Opens) from trivial)
  have hjy : ⊤ ≤ sy ⁻¹ᵁ ((q' ≫ q) ⁻¹ᵁ V j₀) := by
    change ⊤ ≤ ((sy ≫ q') ≫ q) ⁻¹ᵁ V j₀
    rw [show sy ≫ q' = W.ι ≫ sY from hy.lift_fst _ _ _]
    exact fun x _ => hj₀ (show W.ι x ∈ (⊤ : S.Opens) from trivial)
  let ex : (L'.pullback (ProductBaseAxes.Construction.ProductBaseChangeAxes.left f' g' sy hsy)).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (pullback f W.ι) :=
    BaseChanged.Construction.BaseChangedBundleFrames.axis (ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g sY hsY) m p'
      (ProductBaseAxes.Construction.ProductBaseChangeAxes.left f' g' sy hsy)
      (ProductBaseAxes.Construction.ProductBaseChangeAxes.left_square f g f' g' p' q' W.ι hx hy sY hsY).symm L.sheaf eX
  let ey : (L'.pullback (ProductBaseAxes.Construction.ProductBaseChangeAxes.right f' g' sx hsx)).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (pullback g W.ι) :=
    BaseChanged.Construction.BaseChangedBundleFrames.axis (ProductBaseAxes.Construction.ProductBaseChangeAxes.right f g sX hsX) m q'
      (ProductBaseAxes.Construction.ProductBaseChangeAxes.right f' g' sx hsx)
      (ProductBaseAxes.Construction.ProductBaseChangeAxes.right_square f g f' g' p' q' W.ι hx hy sX hsX).symm L.sheaf eY
  have hrs : Set.range s ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    have hz : z = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    exact hz ▸ hsW
  let s' := IsOpenImmersion.lift W.ι s hrs
  have hs' : s' ≫ W.ι = s := IsOpenImmersion.lift_fac _ _ _
  have hs't : s' ≫ (W.ι ≫ t) = 𝟙 _ := by rw [← Category.assoc, hs', hs]
  let er : (L'.pullback (pullback.fst (pullback.fst f' g' ≫ f') s')).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (pullback (pullback.fst f' g' ≫ f') s') :=
    BaseChanged.Construction.BaseChangedBundleFrames.fiber m (pullback.fst f g ≫ f) (pullback.fst f' g' ≫ f')
      W.ι hm s' s hs' L.sheaf he
  obtain ⟨e⟩ := CartesianProductTrivial.Construction.CartesianProductSeesaw.trivial a b DA DB f' g' (p' ≫ p) (q' ≫ q) (W.ι ≫ t)
    (hx.paste_horiz hp) (hy.paste_horiz hq) U V hU hV hcU hcV
    sx hsx sy hsy i₀ hix j₀ hjy L' ex ey s' hs't er
  exact ⟨BaseChanged.Construction.BaseChangedBundleFrames.openFrame m (pullback.fst f g ≫ f) W
    (pullback.fst f' g' ≫ f') hm L.sheaf e⟩

end Construction.OpenCartesianProductSeesaw

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenCartesian
