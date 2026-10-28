import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientChange
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor

/-! # Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Iso

noncomputable section

/-! Isomorphic actual crystalline frames give naturally isomorphic
principal-localization diagrams on the same coefficient category. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))
  {P Q : AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X} (e : P ≅ Q)

local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Q.thickening.ring

def coefficients : C ⥤ AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object P.thickening.ring :=
  Principal.CoefficientChange.functor e.hom.ambientMap.toRingHom

def diagram : C ⥤ AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X :=
  coefficients p k X e ⋙ AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.functor p k X P

def projection (r : C) : (diagram p k X e).obj r ⟶ P :=
  AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X P ((coefficients p k X e).obj r)

instance projection_mono (r : C) : Mono (projection p k X e r) :=
  AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Factorization.CrystallinePrincipalFactorization.projection_mono p k X P (e.hom.ambientMap r.val)

theorem projection_naturality {r s : C} (h : r ⟶ s) :
    (diagram p k X e).map h ≫ projection p k X e s = projection p k X e r :=
  AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map_projection p k X P ((coefficients p k X e).map h)

theorem coefficient_unit (r : C) :
    IsUnit (((projection p k X e r) ≫ e.hom).ambientMap r.val) := by
  change IsUnit (algebraMap P.thickening.ring
    (Localization.Away (e.hom.ambientMap r.val)) (e.hom.ambientMap r.val))
  exact IsLocalization.Away.algebraMap_isUnit _

def map (r : C) : (diagram p k X e).obj r ⟶
    AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q r :=
  AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Factorization.CrystallinePrincipalFactorization.lift p k X (projection p k X e r ≫ e.hom)
    r.val (coefficient_unit p k X e r)

theorem map_projection (r : C) : Iso.map p k X e r ≫
    AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q r = projection p k X e r ≫ e.hom :=
  AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Factorization.CrystallinePrincipalFactorization.lift_projection p k X _ _ _

theorem ambient_inverse (a : Q.thickening.ring) :
    e.inv.ambientMap (e.hom.ambientMap a) = a := by
  have h := congrArg (fun f : Q ⟶ Q => f.ambientMap a) e.inv_hom_id
  exact h

theorem inverse_coefficient_unit (r : C) :
    IsUnit (((AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q r) ≫ e.inv).ambientMap
      (e.hom.ambientMap r.val)) := by
  change IsUnit (algebraMap Q.thickening.ring (Localization.Away r.val)
    (e.inv.ambientMap (e.hom.ambientMap r.val)))
  rw [ambient_inverse]
  exact IsLocalization.Away.algebraMap_isUnit _

def inverse (r : C) : AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q r ⟶
    (diagram p k X e).obj r :=
  AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Factorization.CrystallinePrincipalFactorization.lift p k X
    (AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q r ≫ e.inv)
    (e.hom.ambientMap r.val) (inverse_coefficient_unit p k X e r)

theorem inverse_projection (r : C) : inverse p k X e r ≫ projection p k X e r =
    AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q r ≫ e.inv :=
  AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Factorization.CrystallinePrincipalFactorization.lift_projection p k X _ _ _

def componentIso (r : C) : (diagram p k X e).obj r ≅
    AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q r where
  hom := Iso.map p k X e r
  inv := inverse p k X e r
  hom_inv_id := by
    apply (cancel_mono (projection p k X e r)).mp
    rw [Category.assoc, inverse_projection, ← Category.assoc, map_projection]
    simp
  inv_hom_id := by
    apply (cancel_mono (AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q r)).mp
    rw [Category.assoc, map_projection, ← Category.assoc, inverse_projection]
    simp

def diagramIso : diagram p k X e ≅ AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.functor p k X Q :=
  NatIso.ofComponents (componentIso p k X e) (by
    intro r s h
    apply (cancel_mono (AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q s)).mp
    change ((diagram p k X e).map h ≫ Iso.map p k X e s) ≫ _ =
      (Iso.map p k X e r ≫ AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map p k X Q h) ≫ _
    rw [Category.assoc, map_projection, ← Category.assoc,
      projection_naturality, Category.assoc,
      AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map_projection, map_projection])

theorem map_algebraMap (r : C) (a : Q.thickening.ring) :
    (Iso.map p k X e r).ambientMap (algebraMap Q.thickening.ring (Localization.Away r.val) a) =
      (projection p k X e r).ambientMap (e.hom.ambientMap a) :=
  RingHom.congr_fun (AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Factorization.CrystallinePrincipalFactorization.ambientLift_comp p k X
    (projection p k X e r ≫ e.hom) r.val (coefficient_unit p k X e r)) a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Iso
