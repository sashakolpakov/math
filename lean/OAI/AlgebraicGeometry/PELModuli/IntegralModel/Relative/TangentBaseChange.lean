import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.PointedTangentAt

/-! # Tangent Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.TangentBaseChange

noncomputable section

section

/-! Relative infinitesimal points of arbitrary schemes, their
actual point classification, and the linear map of every commutative square. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace RelativeTangent

variable {C : CommRingCat.{0}} [IsLocalRing C] (J : Ideal C) (hJ : J ^ 2 = ⊥)
  {X Y : Scheme.{0}} (p : Y ⟶ X) (g : Spec C ⟶ Y)

abbrev Space := AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.relativeModule J hJ (Scheme.stalkClosedPointTo g) p

def point (v : Space J hJ p g) : Spec C ⟶ Y := AbelianScheme.TorsionQuotient.PointedTangentAt.PointedTangent.point J hJ g v.val

theorem point_zero : point J hJ p g 0 = g := AbelianScheme.TorsionQuotient.PointedTangentAt.PointedTangent.point_zero J hJ g

theorem point_injective : Function.Injective (point J hJ p g) := by
  intro v w h
  exact Subtype.ext (AbelianScheme.TorsionQuotient.PointedTangentAt.PointedTangent.point_injective J hJ g h)

theorem point_over (v : Space J hJ p g) : point J hJ p g v ≫ p = g ≫ p := by
  have h := AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.toPoint_over J hJ (Scheme.stalkClosedPointTo g) p v
  exact h.trans (congrArg (fun q => q ≫ p) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk g))

theorem mem_iff (v : AbelianScheme.TorsionQuotient.PointedTangentAt.PointedTangent.Space J hJ g) :
    v ∈ AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.relativeModule J hJ (Scheme.stalkClosedPointTo g) p ↔
      AbelianScheme.TorsionQuotient.PointedTangentAt.PointedTangent.point J hJ g v ≫ p = g ≫ p := by
  constructor
  · intro h
    exact point_over J hJ p g ⟨v, h⟩
  · intro h
    let e := Scheme.stalkClosedPointTo g
    let : IsLocalHom (p.stalkMap _ ≫ e).hom :=
      inferInstanceAs (IsLocalHom (e.hom.comp (p.stalkMap _).hom))
    apply AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.toPoint_injective J hJ (p.stalkMap _ ≫ e)
    rw [AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.toPoint_map, AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.toPoint_zero, AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.ofGerm_comp]
    exact h.trans (congrArg (fun q => q ≫ p) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk g)).symm

theorem point_reduction (v : Space J hJ p g) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ point J hJ p g v =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ g :=
  AbelianScheme.TorsionQuotient.PointedTangentAt.PointedTangent.point_reduction J hJ g v.val

theorem exists_point (f : Spec C ⟶ Y)
    (hr : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ f =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ g)
    (hf : f ≫ p = g ≫ p) : ∃ v : Space J hJ p g, point J hJ p g v = f := by
  obtain ⟨v, hv⟩ := AbelianScheme.TorsionQuotient.PointedTangentAt.PointedTangent.exists_point J hJ g f hr
  have hmem := (mem_iff J hJ p g v).mpr ((congrArg (fun q => q ≫ p) hv).trans hf)
  exact ⟨⟨v, hmem⟩, hv⟩

variable {X' Y' : Scheme.{0}} (p' : Y' ⟶ X') (g' : Spec C ⟶ Y')
  (f : Y ⟶ Y') (a : X ⟶ X') (hf : f ≫ p' = p ≫ a) (hg : g ≫ f = g')

def pointedMap : Under.mk g ⟶ Under.mk g' := Under.homMk f hg

def map : Space J hJ p g →ₗ[C] Space J hJ p' g' where
  toFun v := ⟨AbelianScheme.TorsionQuotient.PointedTangentAt.PointedTangent.map J hJ (pointedMap g g' f hg) v.val, by
    apply (mem_iff J hJ p' g' _).mpr
    refine (congrArg (fun q => q ≫ p')
      (AbelianScheme.TorsionQuotient.PointedTangentAt.PointedTangent.point_map J hJ (pointedMap g g' f hg) v.val)).trans ?_
    change (point J hJ p g v ≫ f) ≫ p' = g' ≫ p'
    rw [Category.assoc, hf, ← Category.assoc, point_over,
      Category.assoc, ← hf, ← Category.assoc, hg]⟩
  map_add' v w := Subtype.ext ((AbelianScheme.TorsionQuotient.PointedTangentAt.PointedTangent.map J hJ (pointedMap g g' f hg)).map_add v.val w.val)
  map_smul' c v := Subtype.ext ((AbelianScheme.TorsionQuotient.PointedTangentAt.PointedTangent.map J hJ (pointedMap g g' f hg)).map_smul c v.val)

theorem point_map (v : Space J hJ p g) :
    point J hJ p' g' (RelativeTangent.map J hJ p g p' g' f a hf hg v) = point J hJ p g v ≫ f :=
  AbelianScheme.TorsionQuotient.PointedTangentAt.PointedTangent.point_map J hJ (pointedMap g g' f hg) v.val

end RelativeTangent

end

/-! The actual linear map on relative infinitesimal points of a
cartesian scheme square is bijective, for every local square-zero test ring. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace RelativeTangent

theorem map_bijective_of_isPullback
    {C : CommRingCat.{0}} [IsLocalRing C] (J : Ideal C) (hJ : J ^ 2 = ⊥)
    {X Y X' Y' : Scheme.{0}} (p : Y ⟶ X) (g : Spec C ⟶ Y)
    (p' : Y' ⟶ X') (g' : Spec C ⟶ Y') (f : Y ⟶ Y') (a : X ⟶ X')
    (hP : IsPullback f p p' a) (hg : g ≫ f = g') :
    Function.Bijective (RelativeTangent.map J hJ p g p' g' f a hP.w hg) := by
  constructor
  · intro v w h
    apply point_injective J hJ p g
    apply hP.hom_ext
    · exact (point_map J hJ p g p' g' f a hP.w hg v).symm.trans
        ((congrArg (point J hJ p' g') h).trans (point_map J hJ p g p' g' f a hP.w hg w))
    · exact (point_over J hJ p g v).trans (point_over J hJ p g w).symm
  · intro w
    have hw : point J hJ p' g' w ≫ p' = (g ≫ p) ≫ a := by
      rw [point_over, ← hg, Category.assoc, hP.w, ← Category.assoc]
    obtain ⟨l, hlf, hlp⟩ := hP.exists_lift (point J hJ p' g' w) (g ≫ p) hw
    have hr : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ l =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ g := by
      apply hP.hom_ext
      · rw [Category.assoc, hlf, Category.assoc, hg]
        exact point_reduction J hJ p' g' w
      · rw [Category.assoc, hlp, Category.assoc]
    obtain ⟨v, hv⟩ := exists_point J hJ p g l hr hlp
    refine ⟨v, ?_⟩
    apply point_injective J hJ p' g'
    exact (point_map J hJ p g p' g' f a hP.w hg v).trans
      ((congrArg (fun q => q ≫ f) hv).trans hlf)

end RelativeTangent

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.TangentBaseChange
