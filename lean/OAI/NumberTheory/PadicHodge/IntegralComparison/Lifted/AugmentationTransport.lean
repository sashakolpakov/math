import OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.HomologyCoordinates

/-! # Augmentation Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.AugmentationTransport

noncomputable section

/-! A canonical coefficient lift transports an augmentation-normalized
cohomology comparison back to its literal native complex. -/

open _root_.CategoryTheory

universe u v w t

variable {R : Type u} [CommRing R]
  {A K : CochainComplex (ModuleCat.{v} R) ℕ}
  {T : CochainComplex (ModuleCat.{max v w} R) ℕ}
  (d : T ≅ HomologyCoordinates.complex.{u, v, w} R K)
  (a : HomologyCoordinates.complex.{u, v, w} R A ⟶ T) (b : A ⟶ K)
  (h : a ≫ d.hom = ((ModuleCat.uliftFunctor.{w, v} R).mapHomologicalComplex (.up ℕ)).map b)
  (i : ℕ) {M : Type t} [AddCommGroup M] [Module R M]
  (c : T.homology i →ₗ[R] M)

def comparison : K.homology i →ₗ[R] M :=
  c.comp ((HomologicalComplex.homologyMap d.inv i).hom.comp
    (HomologyCoordinates.equivalence.{u, v, w} R K i).toLinearMap)

variable (e : (HomologyCoordinates.complex.{u, v, w} R A).homology i →ₗ[R] M)
  (he : ∀ x, c (HomologicalComplex.homologyMap a i x) = e x)

include h he in
theorem augmentation (x : A.homology i) :
    comparison d i c (HomologicalComplex.homologyMap b i x) =
      e (HomologyCoordinates.equivalence.{u, v, w} R A i x) := by
  have hs : a ≫ d.hom = (Iso.refl _).hom ≫
      ((ModuleCat.uliftFunctor.{w, v} R).mapHomologicalComplex (.up ℕ)).map b :=
    h.trans (Category.id_comp _).symm
  have hh := InverseCoordinateHomology.homology (Iso.refl _) d a
    (((ModuleCat.uliftFunctor.{w, v} R).mapHomologicalComplex (.up ℕ)).map b) hs i
  simp only [Iso.refl_inv, HomologicalComplex.homologyMap_id, Category.id_comp] at hh
  have hx := congrArg (fun f => f (HomologyCoordinates.equivalence.{u, v, w} R A i x)) hh
  exact (congrArg c
    ((congrArg (HomologicalComplex.homologyMap d.inv i)
      (HomologyCoordinates.naturality.{u, v, w} R b i x).symm).trans hx)).trans (he _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.AugmentationTransport
