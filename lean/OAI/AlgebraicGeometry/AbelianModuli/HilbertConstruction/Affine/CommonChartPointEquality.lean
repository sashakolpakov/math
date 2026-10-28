import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-! # Common Chart Point Equality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CommonChartPointEquality

noncomputable section

/-! Equality of relative points can be checked on affine common
factorizations through the actual charts of an open target cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

private def chartFactorOver
    {S : Scheme.{u}} {T X Y : Over S} {V : Scheme.{u}}
    (a : T ⟶ Y) (j : X ⟶ Y) (r : V ⟶ T.left) (b : V ⟶ X.left)
    (h : b ≫ j.left = r ≫ a.left) : Over.mk (r ≫ T.hom) ⟶ X :=
  Over.homMk b
    ((congrArg (fun t => b ≫ t) j.w.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ Y.hom) h).trans
          ((Category.assoc _ _ _).trans (congrArg (fun t => r ≫ t) a.w)))))

/-- Pull back the target cover along both points, then pass to the
affine cover of each common pullback. The original chart maps and
their factorizations are retained on every resulting test scheme. -/
theorem overHom_eq_of_affine_common_chart_factors
    {S : Scheme.{u}} {T G : Over S} [IsLocallyNoetherian T.left]
    {J : Type u} (U : J → Over S) (ι : ∀ j, U j ⟶ G)
    [∀ j, IsOpenImmersion (ι j).left]
    (covers : ∀ x : G.left, ∃ j, ∃ y : (U j).left, (ι j).left y = x)
    (a b : T ⟶ G)
    (h : ∀ (V : Over S) [IsAffine V.left] [IsLocallyNoetherian V.left]
      (r : V ⟶ T) (j k : J) (av : V ⟶ U j) (bv : V ⟶ U k),
      av ≫ ι j = r ≫ a → bv ≫ ι k = r ≫ b → av ≫ ι j = bv ≫ ι k) :
    a = b := by
  let C : G.left.OpenCover := Scheme.Cover.mkOfCovers J
    (fun j => (U j).left) (fun j => (ι j).left) covers
  let Ca : T.left.OpenCover := C.pullback₁ a.left
  apply Over.OverMorphism.ext
  apply Ca.hom_ext
  intro j
  change J at j
  let X := Ca.X j
  let p : X ⟶ T.left := Ca.f j
  let aj : X ⟶ (U j).left := C.pullbackHom a.left j
  let : IsOpenImmersion p := Ca.map_prop j
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isOpenImmersion p
  let b' : X ⟶ G.left := p ≫ b.left
  let Cb : X.OpenCover := C.pullback₁ b'
  apply Cb.hom_ext
  intro k
  change J at k
  let Y := Cb.X k
  let s : Y ⟶ X := Cb.f k
  let bk : Y ⟶ (U k).left := C.pullbackHom b' k
  let : IsOpenImmersion s := Cb.map_prop k
  let : IsLocallyNoetherian Y := isLocallyNoetherian_of_isOpenImmersion s
  apply Y.affineOpenCover.openCover.hom_ext
  intro l
  change Y.affineOpenCover.I₀ at l
  let V := Y.affineOpenCover.openCover.X l
  let w : V ⟶ Y := Y.affineOpenCover.f l
  let r : V ⟶ T.left := w ≫ s ≫ p
  let av : V ⟶ (U j).left := w ≫ s ≫ aj
  let bv : V ⟶ (U k).left := w ≫ bk
  have ha : av ≫ (ι j).left = r ≫ a.left := by
    have hp : aj ≫ (ι j).left = p ≫ a.left :=
      C.pullbackHom_map a.left j
    change (w ≫ s ≫ aj) ≫ (ι j).left = (w ≫ s ≫ p) ≫ a.left
    simpa only [Category.assoc] using congrArg (fun t => w ≫ s ≫ t) hp
  have hb : bv ≫ (ι k).left = r ≫ b.left := by
    have hs : bk ≫ (ι k).left = s ≫ (p ≫ b.left) :=
      C.pullbackHom_map b' k
    change (w ≫ bk) ≫ (ι k).left = (w ≫ s ≫ p) ≫ b.left
    simpa only [Category.assoc] using congrArg (fun t => w ≫ t) hs
  let V₀ : Over S := Over.mk (r ≫ T.hom)
  let : IsAffine V₀.left := inferInstanceAs (IsAffine (Spec (Y.affineOpenCover.X l)))
  let : IsOpenImmersion w := Y.affineOpenCover.map_prop l
  let : IsLocallyNoetherian V₀.left := isLocallyNoetherian_of_isOpenImmersion w
  let r₀ : V₀ ⟶ T := Over.homMk r rfl
  let a₀ : V₀ ⟶ U j := chartFactorOver a (ι j) r av ha
  let b₀ : V₀ ⟶ U k := chartFactorOver b (ι k) r bv hb
  have ha₀ : a₀ ≫ ι j = r₀ ≫ a := Over.OverMorphism.ext ha
  have hb₀ : b₀ ≫ ι k = r₀ ≫ b := Over.OverMorphism.ext hb
  have he : a₀ ≫ ι j = b₀ ≫ ι k := h V₀ r₀ j k a₀ b₀ ha₀ hb₀
  have hr : r ≫ a.left = r ≫ b.left :=
    ha.symm.trans ((congrArg Over.Hom.left he).trans hb)
  change w ≫ (s ≫ (p ≫ a.left)) = w ≫ (s ≫ (p ≫ b.left))
  simpa only [r, Category.assoc] using hr

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CommonChartPointEquality
