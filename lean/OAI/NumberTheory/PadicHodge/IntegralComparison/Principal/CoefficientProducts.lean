import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientChange

/-! # Coefficient Products -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientProducts

noncomputable section

/-! A ring homomorphism preserves the finite intersections in the
actual principal-coefficient category, including its terminal object. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory
universe u v w
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
  (f : A →+* B)

theorem opens_product {ι : Type w} [Fintype ι] (r : ι → AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object A) :
    AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.opens B ((CoefficientChange.functor f).obj (AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.product A r)) =
      ⨅ i, AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.opens B ((CoefficientChange.functor f).obj (r i)) := by
  change PrimeSpectrum.basicOpen (f (∏ i, (r i).val)) =
    ⨅ i, PrimeSpectrum.basicOpen (f (r i).val)
  rw [map_prod]
  exact AlgebraicGeometry.Crystalline.Cohomology.Finite.PrincipalIntersections.FinitePrincipalIntersections.basicOpen_prod B (fun i => f (r i).val)

def mappedConeIsLimit {J : Type w} [Category J] [Fintype J] (F : J ⥤ AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object A) :
    IsLimit ((CoefficientChange.functor f).mapCone (AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.finiteLimitCone A F).cone) where
  lift c := homOfLE (by
    change AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.opens B c.pt ≤ AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.opens B ((CoefficientChange.functor f).obj (AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.product A F.obj))
    rw [opens_product]
    exact le_iInf (fun j => leOfHom (c.π.app j)))

instance preserves : PreservesFiniteLimits (CoefficientChange.functor f) := ⟨by
  intro J _ _
  exact { preservesLimit := fun {F} =>
    preservesLimit_of_preserves_limit_cone (AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.finiteLimitCone A F).isLimit (mappedConeIsLimit f F) }⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientProducts
