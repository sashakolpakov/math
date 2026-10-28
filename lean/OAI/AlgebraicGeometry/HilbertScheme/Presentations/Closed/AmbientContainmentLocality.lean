import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ClosedAmbientRange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.AmbientCover
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.ContainmentOpenLocality

/-! # Ambient Containment Locality -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.AmbientContainmentLocality.Hilbert

noncomputable section

/-! The exact closed-ambient containment condition on native Hilbert
families is local on arbitrary open covers of the test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {X Y : Over S} (j : X ⟶ Y) [IsClosedImmersion j.left]

theorem ambientEmbedding_ker_baseChange {T U : Over S} (a : T ⟶ U) :
    (Hilbert.ClosedAmbientMap.ambientEmbedding j T).ker = (Hilbert.ClosedAmbientMap.ambientEmbedding j U).ker.comap (Hilbert.Functor.ambientMap Y a) := by
  let h := Hilbert.ClosedAmbientNaturality.ambientEmbedding_baseChange j a
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

variable {T : Over S} {ι : Type u} (U : ι → Over S) (f : ∀ i, U i ⟶ T)
variable [∀ i, IsOpenImmersion (f i).left]
variable (hcover : ∀ t : T.left, ∃ i, ∃ u : (U i).left, (f i).left u = t)

include hcover in
theorem closedAmbientHilbertLocus_of_openCover (F : Hilbert.Functor.Family Y T)
    (h : ∀ i, Hilbert.Functor.pullbackFamily Y (f i) F ∈ (Hilbert.ClosedAmbientRange.closedAmbientHilbertLocus j).obj (.op (U i))) :
    F ∈ (Hilbert.ClosedAmbientRange.closedAmbientHilbertLocus j).obj (.op T) := by
  apply (Hilbert.ClosedAmbientRange.closedAmbientHilbertLocus_mem j F).mpr
  apply Ideal.ContainmentOpenLocality.ideal_le_of_openCover (Hilbert.AmbientCover.ambientOpenCover Y U f hcover)
  intro i
  have hi := (Hilbert.ClosedAmbientRange.closedAmbientHilbertLocus_mem j (Hilbert.Functor.pullbackFamily Y (f i) F)).mp (h i)
  rw [ambientEmbedding_ker_baseChange] at hi
  exact hi

include hcover in
theorem closedAmbientHilbertLocus_iff_openCover (F : Hilbert.Functor.Family Y T) :
    F ∈ (Hilbert.ClosedAmbientRange.closedAmbientHilbertLocus j).obj (.op T) ↔
      ∀ i, Hilbert.Functor.pullbackFamily Y (f i) F ∈ (Hilbert.ClosedAmbientRange.closedAmbientHilbertLocus j).obj (.op (U i)) :=
  ⟨fun h i => (Hilbert.ClosedAmbientRange.closedAmbientHilbertLocus j).map (f i).op h,
    closedAmbientHilbertLocus_of_openCover j U f hcover F⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.AmbientContainmentLocality.Hilbert
