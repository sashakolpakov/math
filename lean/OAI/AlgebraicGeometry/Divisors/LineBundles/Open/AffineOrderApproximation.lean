import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrimeOrderApproximation
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.FunctionFieldUnits

/-! # Affine Order Approximation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.AffineOrderApproximation.BundleCycles

noncomputable section

/-! # LineBundleCycles: rational-order approximation on an actual common affine neighborhood -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {X : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]

theorem exists_openAffine_prescribed_orders {ι : Type*} [Finite ι]
    (x : ι → Spec (CommRingCat.of R)) (hx : ∀ i, coheight (j (x i)) = 1)
    (hinj : Function.Injective x) [∀ i, IsIntegrallyClosed (X.presheaf.stalk (j (x i)))]
    (n : ι → ℤ) : ∃ g : X.functionFieldˣ, ∀ i, X.ord (g : X.functionField) (j (x i)) = n i := by
  let : ∀ i, IsIntegrallyClosed ((Spec (CommRingCat.of R)).presheaf.stalk (x i)) :=
    fun i => IsIntegrallyClosed.of_equiv (asIso (j.stalkMap (x i))).commRingCatIsoToRingEquiv
  have hx' : ∀ i, coheight (x i) = 1 := fun i =>
    (coheight_eq_of_isOpenImmersion j).symm.trans (hx i)
  obtain ⟨g, hg⟩ := Affine.PrimeOrderApproximation.BundleCycles.exists_affine_prescribed_orders x hx' hinj n
  let a : X.functionFieldˣ := Units.map (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso j).inv.hom.toMonoidHom g
  have ha : FunctionFieldUnits.BundleCycles.openFunctionFieldUnits j a = g := by
    apply Units.ext
    exact Iso.inv_hom_id_apply (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso j) g.val
  refine ⟨a, fun i => ?_⟩
  rw [← FunctionFieldUnits.BundleCycles.openFunctionFieldUnits_order j a (x i), ha]
  exact hg i

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.AffineOrderApproximation.BundleCycles
