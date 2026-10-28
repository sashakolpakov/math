import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.PrincipalIntersections
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! # Principal Coefficient -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory

noncomputable section

/-!
# A category of principal-open coefficients

Objects retain their defining ring coefficient; a morphism is inclusion
of the corresponding principal opens. Products of coefficients supply
finite limits. The functor to actual affine opens preserves those limits.
This keeps explicit localization rings available throughout a Čech nerve.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry PrimeSpectrum

universe u v

variable (R : Type u) [CommRing R]

structure Object where
  val : R

def opens (r : Object R) : (Spec (CommRingCat.of R)).Opens := basicOpen r.val

instance : Preorder (Object R) where
  le r s := opens R r ≤ opens R s
  le_refl _ := le_rfl
  le_trans _ _ _ := le_trans

def opensFunctor : Object R ⥤ (Spec (CommRingCat.of R)).Opens where
  obj := opens R
  map f := homOfLE (leOfHom f)

def product {α : Type v} [Fintype α] (r : α → Object R) : Object R :=
  ⟨∏ i, (r i).val⟩

theorem opens_product {α : Type v} [Fintype α] (r : α → Object R) :
    opens R (product R r) = ⨅ i, opens R (r i) :=
  Cohomology.Finite.PrincipalIntersections.FinitePrincipalIntersections.basicOpen_prod R (fun i => (r i).val)

def finiteLimitCone {J : Type v} [Category J] [Fintype J] (F : J ⥤ Object R) : LimitCone F where
  cone :=
    { pt := product R F.obj
      π :=
        { app j := homOfLE (by
            change opens R (product R F.obj) ≤ opens R (F.obj j)
            rw [opens_product]
            exact iInf_le _ j) } }
  isLimit :=
    { lift c := homOfLE (by
        change opens R c.pt ≤ opens R (product R F.obj)
        rw [opens_product]
        exact le_iInf (fun j => leOfHom (c.π.app j))) }

instance : HasFiniteLimits (Object R) := ⟨by
  intro J _ _
  exact { has_limit := fun F => HasLimit.mk (finiteLimitCone R F) }⟩

def mappedConeIsLimit {J : Type v} [Category J] [Fintype J] (F : J ⥤ Object R) :
    IsLimit ((opensFunctor R).mapCone (finiteLimitCone R F).cone) where
  lift c := homOfLE (by
    change c.pt ≤ opens R (product R F.obj)
    rw [opens_product]
    exact le_iInf (fun j => leOfHom (c.π.app j)))

instance : PreservesFiniteLimits (opensFunctor R) := ⟨by
  intro J _ _
  exact { preservesLimit := fun {F} =>
    preservesLimit_of_preserves_limit_cone (finiteLimitCone R F).isLimit (mappedConeIsLimit R F) }⟩

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory
