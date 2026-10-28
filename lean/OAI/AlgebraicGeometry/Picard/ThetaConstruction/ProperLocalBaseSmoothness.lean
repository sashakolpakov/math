import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Proper Local Base Smoothness -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.ProperLocalBaseSmoothness.Geometric

noncomputable section

/-! A closed map to the spectrum of a local ring has no nonempty closed
subset avoiding the closed fiber. Thus an open smooth locus containing
that entire fiber is the whole source. -/

open Set _root_.CategoryTheory _root_.AlgebraicGeometry

theorem open_eq_univ_of_closed_fiber {R X : Type*} [CommRing R] [IsLocalRing R]
    [TopologicalSpace X] (f : X → PrimeSpectrum R) (hf : IsClosedMap f)
    (U : Set X) (hU : IsOpen U)
    (hfiber : ∀ x, f x = IsLocalRing.closedPoint R → x ∈ U) : U = univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_contra hx
  have hc : IsClosed (f '' Uᶜ) := hf Uᶜ hU.isClosed_compl
  have hm : IsLocalRing.closedPoint R ∈ f '' Uᶜ :=
    (IsLocalRing.specializes_closedPoint (f x)).mem_closed hc ⟨x, hx, rfl⟩
  obtain ⟨y, hy, he⟩ := hm
  exact hy (hfiber y he)

theorem scheme_smooth_of_entire_closed_fiber {R : Type} [CommRing R] [IsLocalRing R]
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of R)) [UniversallyClosed f] [LocallyOfFinitePresentation f]
    (hfiber : ∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ f.smoothLocus) : Smooth f := by
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  apply TopologicalSpace.Opens.ext
  exact open_eq_univ_of_closed_fiber f f.isClosedMap f.smoothLocus f.smoothLocus.isOpen hfiber

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.ProperLocalBaseSmoothness.Geometric
