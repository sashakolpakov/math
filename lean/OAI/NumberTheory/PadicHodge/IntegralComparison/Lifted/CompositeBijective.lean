import OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.AugmentationTransport

/-! # Composite Bijective -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.CompositeBijective

noncomputable section

/-! A normalized lifted comparison makes its whole native composite
bijective, without separately assuming the target comparison invertible. -/

open _root_.CategoryTheory

universe u v w t
variable {R : Type u} [CommRing R]
  {A K : CochainComplex (ModuleCat.{v} R) ℕ}
  {T : CochainComplex (ModuleCat.{max v w} R) ℕ}
  (d : T ≅ HomologyCoordinates.complex.{u,v,w} R K)
  (a : HomologyCoordinates.complex.{u,v,w} R A ⟶ T) (b : A ⟶ K)
  (h : a ≫ d.hom = ((ModuleCat.uliftFunctor.{w,v} R).mapHomologicalComplex (.up ℕ)).map b)
  (i : ℕ) {M : Type t} [AddCommGroup M] [Module R M]
  (c : T.homology i →ₗ[R] M)
  (e : (HomologyCoordinates.complex.{u,v,w} R A).homology i →ₗ[R] M)
  (he : ∀ x, c (HomologicalComplex.homologyMap a i x) = e x)
  (hebij : Function.Bijective e)

include h he hebij in
theorem bijective : Function.Bijective
    ((AugmentationTransport.comparison d i c).comp
      (HomologicalComplex.homologyMap b i).hom) := by
  have hfun : ((AugmentationTransport.comparison d i c).comp
      (HomologicalComplex.homologyMap b i).hom : A.homology i → M) =
      fun x => e (HomologyCoordinates.equivalence.{u,v,w} R A i x) :=
    funext (AugmentationTransport.augmentation d a b h i c e he)
  rw [hfun]
  exact hebij.comp (HomologyCoordinates.equivalence.{u,v,w} R A i).bijective

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.CompositeBijective
