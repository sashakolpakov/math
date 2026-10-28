import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor

/-! # Slice -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Slice.CrystallinePrincipalSlice

noncomputable section

/-!
# Principal-open intersections in the native crystalline slice

The principal-object functor preserves finite limits over its original
crystalline object. A cone makes every defining coefficient invertible;
their product is invertible, giving the required PD-localization lift.
The native projection monomorphisms give uniqueness.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u v

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q : Site.Object p k X)

local notation "QR" => Q.thickening.ring

def functor : PrincipalCoefficient.PrincipalCoefficientCategory.Object QR ⥤ Over Q :=
  (Functor.CrystallinePrincipalFunctor.functor p k X Q).toOver Q
    (Functor.CrystallinePrincipalFunctor.projection p k X Q)
    (fun f => Functor.CrystallinePrincipalFunctor.map_projection p k X Q f)

instance hom_subsingleton (r : PrincipalCoefficient.PrincipalCoefficientCategory.Object QR) (Z : Over Q) :
    Subsingleton (Z ⟶ (functor p k X Q).obj r) := by
  refine ⟨fun f g => ?_⟩
  apply (Over.forget Q).map_injective
  apply (cancel_mono (Functor.CrystallinePrincipalFunctor.projection p k X Q r)).mp
  exact (Over.w f).trans (Over.w g).symm

variable {J : Type v} [Category J] [Fintype J]
  (F : J ⥤ PrincipalCoefficient.PrincipalCoefficientCategory.Object Q.thickening.ring)

omit [Fintype J] in
theorem cone_coefficient_unit (c : Cone (F ⋙ functor p k X Q)) (j : J) :
    IsUnit (c.pt.hom.ambientMap (F.obj j).val) := by
  have hu := (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (F.obj j).val)
    (F.obj j).val).map (c.π.app j).left.ambientMap.toRingHom
  have he := congrArg (fun h : c.pt.left ⟶ Q => h.ambientMap (F.obj j).val) (Over.w (c.π.app j))
  exact he ▸ hu

theorem cone_product_unit (c : Cone (F ⋙ functor p k X Q)) :
    IsUnit (c.pt.hom.ambientMap (PrincipalCoefficient.PrincipalCoefficientCategory.product QR F.obj).val) := by
  change IsUnit (c.pt.hom.ambientMap (∏ j, (F.obj j).val))
  rw [map_prod]
  exact IsUnit.prod_univ_iff.mpr (fun j => cone_coefficient_unit p k X Q F c j)

def coneLift (c : Cone (F ⋙ functor p k X Q)) :
    c.pt ⟶ (functor p k X Q).obj (PrincipalCoefficient.PrincipalCoefficientCategory.finiteLimitCone QR F).cone.pt :=
  Over.homMk (Factorization.CrystallinePrincipalFactorization.lift p k X c.pt.hom
    (PrincipalCoefficient.PrincipalCoefficientCategory.product QR F.obj).val (cone_product_unit p k X Q F c))
    (Factorization.CrystallinePrincipalFactorization.lift_projection p k X c.pt.hom
      (PrincipalCoefficient.PrincipalCoefficientCategory.product QR F.obj).val (cone_product_unit p k X Q F c))

def mappedConeIsLimit :
    IsLimit ((functor p k X Q).mapCone (PrincipalCoefficient.PrincipalCoefficientCategory.finiteLimitCone QR F).cone) where
  lift := coneLift p k X Q F
  fac c j := @Subsingleton.elim _ (hom_subsingleton p k X Q (F.obj j) c.pt) _ _
  uniq c _ _ := @Subsingleton.elim _
    (hom_subsingleton p k X Q (PrincipalCoefficient.PrincipalCoefficientCategory.product QR F.obj) c.pt) _ _

instance : PreservesFiniteLimits (functor p k X Q) := ⟨by
  intro J _ _
  exact { preservesLimit := fun {F} =>
    preservesLimit_of_preserves_limit_cone (PrincipalCoefficient.PrincipalCoefficientCategory.finiteLimitCone QR F).isLimit (mappedConeIsLimit p k X Q F) }⟩

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Slice.CrystallinePrincipalSlice
