import OAI.AlgebraicGeometry.Divisors.LineBundles.PrimeFiltration

/-! # Subquotient Image -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SubquotientImage.BundleCycles

noncomputable section

/-!
# LineBundleCycles: successive factors as actual quotient submodules

The factor L/(N ∩ L) is canonically the image of L in M/N. This
identification lets the multiplication exact sequence act on each
successive factor of the constructed prime filtration.
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def subquotientImageEquiv (N L : Submodule R M) :
    (L ⧸ N.comap L.subtype) ≃ₗ[R] L.map N.mkQ := by
  let g : L →ₗ[R] M ⧸ N := N.mkQ.comp L.subtype
  have hk : g.ker = N.comap L.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hr : g.range = L.map N.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  exact (Submodule.quotEquivOfEq _ _ hk.symm).trans
    (g.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hr))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SubquotientImage.BundleCycles
