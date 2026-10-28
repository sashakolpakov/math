import OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.AugmentationTransport

/-! # Bijective -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.Bijective.Comparison

noncomputable section

/-! The native comparison inherited from a bijective lifted comparison
is itself bijective; both coordinate maps are the original ones. -/

open _root_.CategoryTheory

universe u v w t
variable {R : Type u} [CommRing R]
  {K : CochainComplex (ModuleCat.{v} R) ℕ}
  {T : CochainComplex (ModuleCat.{max v w} R) ℕ}
  (d : T ≅ HomologyCoordinates.complex.{u,v,w} R K)
  (i : ℕ) {M : Type t} [AddCommGroup M] [Module R M]
  (c : T.homology i →ₗ[R] M)

theorem bijective (hc : Function.Bijective c) :
    Function.Bijective (AugmentationTransport.comparison d i c) :=
  hc.comp ((HomologicalComplex.homologyMapIso d.symm i).toLinearEquiv.bijective.comp
    (HomologyCoordinates.equivalence.{u,v,w} R K i).bijective)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.Bijective.Comparison
