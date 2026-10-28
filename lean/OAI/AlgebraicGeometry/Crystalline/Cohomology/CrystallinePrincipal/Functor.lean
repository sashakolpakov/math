import OAI.AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Factorization

/-! # Functor -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor

noncomputable section

/-!
# The native crystalline diagram of principal opens

Inclusion of principal opens induces the actual PD localization morphism.
The monomorphism property of the projections verifies the functor laws
and gives a natural projection to the original crystalline object.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q : Site.Object p k X)

local notation "QR" => Q.thickening.ring

def object (r : PrincipalCoefficient.PrincipalCoefficientCategory.Object QR) : Site.Object p k X :=
  Opens.CrystallinePrincipalOpens.object p k X Q r.val

def projection (r : PrincipalCoefficient.PrincipalCoefficientCategory.Object QR) : object p k X Q r ⟶ Q :=
  Opens.CrystallinePrincipalOpens.projection p k X Q r.val

theorem coefficient_unit {r s : PrincipalCoefficient.PrincipalCoefficientCategory.Object QR} (f : r ⟶ s) :
    IsUnit ((projection p k X Q r).ambientMap s.val) := by
  change IsUnit (algebraMap QR (Localization.Away r.val) s.val)
  exact (PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit
    (S := Localization.Away r.val)).mp (leOfHom f)

def map {r s : PrincipalCoefficient.PrincipalCoefficientCategory.Object QR} (f : r ⟶ s) :
    object p k X Q r ⟶ object p k X Q s :=
  Factorization.CrystallinePrincipalFactorization.lift p k X (projection p k X Q r) s.val
    (coefficient_unit p k X Q f)

theorem map_projection {r s : PrincipalCoefficient.PrincipalCoefficientCategory.Object QR} (f : r ⟶ s) :
    CrystallinePrincipalFunctor.map p k X Q f ≫ projection p k X Q s = projection p k X Q r :=
  Factorization.CrystallinePrincipalFactorization.lift_projection p k X (projection p k X Q r) s.val
    (coefficient_unit p k X Q f)

instance (r : PrincipalCoefficient.PrincipalCoefficientCategory.Object QR) : Mono (projection p k X Q r) :=
  Factorization.CrystallinePrincipalFactorization.projection_mono p k X Q r.val

def functor : PrincipalCoefficient.PrincipalCoefficientCategory.Object QR ⥤ Site.Object p k X where
  obj := object p k X Q
  map f := CrystallinePrincipalFunctor.map p k X Q f
  map_id r := by
    apply (cancel_mono (projection p k X Q r)).mp
    rw [map_projection, Category.id_comp]
  map_comp f g := by
    apply (cancel_mono (projection p k X Q _)).mp
    rw [map_projection, Category.assoc, map_projection, map_projection]

def projectionNat : functor p k X Q ⟶ (Functor.const _).obj Q where
  app := projection p k X Q
  naturality _ _ f := (map_projection p k X Q f).trans (Category.comp_id _).symm

theorem map_algebraMap {r s : PrincipalCoefficient.PrincipalCoefficientCategory.Object QR} (f : r ⟶ s) (x : QR) :
    (CrystallinePrincipalFunctor.map p k X Q f).ambientMap (algebraMap QR (Localization.Away s.val) x) =
      algebraMap QR (Localization.Away r.val) x :=
  RingHom.congr_fun (Factorization.CrystallinePrincipalFactorization.ambientLift_comp p k X
    (projection p k X Q r) s.val (coefficient_unit p k X Q f)) x

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor
