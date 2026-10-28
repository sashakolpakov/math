import OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.CompositeBijective

/-! # Section Composite Bijective -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.SectionCompositeBijective

noncomputable section

/-! A genuine source section quasi-isomorphism certifies the complete
normalized native comparison, through its literal cohomology square. -/

open _root_.CategoryTheory

universe u v w
variable {R : Type u} [CommRing R]
  {M K : CochainComplex (ModuleCat.{v} R) ℕ}
  {T S : CochainComplex (ModuleCat.{max v w} R) ℕ}
  (d : T ≅ HomologyCoordinates.complex.{u,v,w} R K)
  (a : HomologyCoordinates.complex.{u,v,w} R M ⟶ T)
  (b : M ⟶ K)
  (h : a ≫ d.hom = ((ModuleCat.uliftFunctor.{w,v} R).mapHomologicalComplex (.up ℕ)).map b)
  (r : HomologyCoordinates.complex.{u,v,w} R M ⟶ S)
  (Z : ℕ → ModuleCat.{max v w} R)
  (e : ∀ i, S.homology i ≅ Z i)
  (c : ∀ i, T.homology i ⟶ Z i)
  (he : ∀ i, HomologicalComplex.homologyMap a i ≫ c i =
    HomologicalComplex.homologyMap r i ≫ (e i).hom)
  (hr : QuasiIso r)

include h he hr in
theorem bijective (i : ℕ) : Function.Bijective
    ((AugmentationTransport.comparison d i (c i).hom).comp
      (HomologicalComplex.homologyMap b i).hom) := by
  let := hr
  exact CompositeBijective.bijective d a b h i (c i).hom
    (HomologicalComplex.homologyMap r i ≫ (e i).hom).hom
    (fun x => ConcreteCategory.congr_hom (he i) x)
    (asIso (HomologicalComplex.homologyMap r i ≫ (e i).hom)).toLinearEquiv.bijective

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.SectionCompositeBijective
