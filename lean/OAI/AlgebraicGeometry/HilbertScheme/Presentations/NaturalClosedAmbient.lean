import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.AmbientContainmentLocus
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.AmbientContainmentLocality
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RepresentedIntersectionTransfer

/-! # Natural Closed Ambient -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.NaturalClosedAmbient.Hilbert

noncomputable section

/-! A natural projective Hilbert family restricts to a closed ambient
subscheme along an actual closed parameter locus, naturally on all tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {X Y H : Over S}

theorem naturalFamily_eq_pullback
    (t : yoneda.obj H ⟶ Hilbert.Functor.familyFunctor Y) {T : Over S} (a : T ⟶ H) :
    t.app (.op T) a = Hilbert.Functor.pullbackFamily Y a (t.app (.op H) (𝟙 H)) := by
  have h := ConcreteCategory.congr_hom (t.naturality a.op) (𝟙 H)
  change t.app (.op T) (a ≫ 𝟙 H) = Hilbert.Functor.pullbackFamily Y a (t.app (.op H) (𝟙 H)) at h
  simpa only [Category.comp_id] using h

theorem naturalFamily_closedAmbient_lifts
    [IsLocallyNoetherian H.left] (BY : Has.Core.ProjectivePresentation Y)
    (i : X ⟶ Y) [IsClosedImmersion i.left] (t : yoneda.obj H ⟶ Hilbert.Functor.familyFunctor Y) :
    ∃ (Z : Over S) (j : Z ⟶ H), IsClosedImmersion j.left ∧
      ∀ (T : Over S) (a : T ⟶ H),
        t.app (.op T) a ∈ (Hilbert.ClosedAmbientRange.closedAmbientHilbertLocus i).obj (.op T) ↔
          ∃! b : T ⟶ Z, b ≫ j = a := by
  let F := t.app (.op H) (𝟙 H)
  obtain ⟨Z, j, hj, htest, _⟩ := Projective.AmbientContainmentLocus.Core.projective_ambient_containment_closed_locus
    BY F (Hilbert.ClosedAmbientMap.ambientEmbedding i H).ker
  refine ⟨Z, j, hj, ?_⟩
  intro T a
  have hmem := Hilbert.ClosedAmbientRange.closedAmbientHilbertLocus_mem i (t.app (.op T) a)
  rw [naturalFamily_eq_pullback, Closed.AmbientContainmentLocality.Hilbert.ambientEmbedding_ker_baseChange] at hmem
  rw [naturalFamily_eq_pullback t a]
  exact hmem.trans (htest T a)

theorem naturalFamily_closedAmbient
    [IsLocallyNoetherian H.left] (BY : Has.Core.ProjectivePresentation Y)
    (i : X ⟶ Y) [IsClosedImmersion i.left]
    (t : yoneda.obj H ⟶ Hilbert.Functor.familyFunctor Y) [Mono t] :
    ∃ (Z : Over S) (j : Z ⟶ H), IsClosedImmersion j.left ∧
      ∃ e : yoneda.obj Z ≅ ((Subfunctor.range t).preimage (Hilbert.ClosedAmbientNaturality.closedAmbientTransformation i)).toFunctor,
        e.hom ≫ ((Subfunctor.range t).preimage (Hilbert.ClosedAmbientNaturality.closedAmbientTransformation i)).ι ≫
          Hilbert.ClosedAmbientNaturality.closedAmbientTransformation i = yoneda.map j ≫ t := by
  obtain ⟨Z, j, hj, htest⟩ := naturalFamily_closedAmbient_lifts BY i t
  let : IsClosedImmersion j.left := hj
  let : Mono j := Over.mono_of_mono_left j
  let : Mono (Hilbert.ClosedAmbientNaturality.closedAmbientTransformation i) := Hilbert.ClosedAmbientNaturality.closedAmbientTransformation_mono i
  refine ⟨Z, j, hj, ?_⟩
  apply RepresentedIntersectionTransfer.representedIntersectionTransfer t (Hilbert.ClosedAmbientNaturality.closedAmbientTransformation i) j
  intro T a
  constructor
  · intro ha
    exact ((htest T a).mp ha).exists
  · rintro ⟨b, hb⟩
    exact (htest T a).mpr ⟨b, hb, fun c hc => (cancel_mono j).mp (hc.trans hb.symm)⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.NaturalClosedAmbient.Hilbert
