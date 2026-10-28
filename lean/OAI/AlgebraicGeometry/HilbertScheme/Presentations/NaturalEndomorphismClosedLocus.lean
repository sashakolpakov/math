import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.EndomorphismEquations
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RepresentedIntersectionTransfer
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # Natural Endomorphism Closed Locus -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.NaturalEndomorphismClosedLocus.Core

noncomputable section

/-! The actual closed group-compatibility locus in a represented family
of morphism tuples represents exactly the corresponding endomorphism tuples. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (A : Over S) [GrpObj A] (n : ℕ)

theorem forgetGroupLaw_injective (T : Over S) :
    Function.Injective ((Endomorphisms.Core.forgetGroupLaw A n).app (.op T)) := by
  intro f g h
  funext i
  exact Subtype.ext (congrFun h i)

theorem forgetGroupLaw_mono : Mono (Endomorphisms.Core.forgetGroupLaw A n) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro T
  exact (CategoryTheory.mono_iff_injective _).mpr (forgetGroupLaw_injective A n T.unop)

theorem preservesGroupLaws_iff_exists_endomorphismTuple {T : Over S}
    (f : (Has.Core.morphismTuples A A n).obj (.op T)) :
    (∀ i, Endomorphisms.Core.PreservesGroupLaw A (f i)) ↔
      ∃ g : (Endomorphisms.Core.endomorphismTuples A n).obj (.op T), (Endomorphisms.Core.forgetGroupLaw A n).app (.op T) g = f := by
  constructor
  · intro h
    exact ⟨fun i => ⟨f i, h i⟩, rfl⟩
  · rintro ⟨g, rfl⟩
    exact fun i => (g i).property

variable [Flat A.hom] [IsProper A.hom] [LocallyOfFinitePresentation A.hom]

theorem naturalMorphism_endomorphismClosed (BA : Has.Core.ProjectivePresentation A)
    {M : Over S} [IsLocallyNoetherian M.left]
    (t : yoneda.obj M ⟶ Has.Core.morphismTuples A A n) [Mono t] :
    ∃ (E : Over S) (j : E ⟶ M), IsClosedImmersion j.left ∧
      (∀ (T : Over S) (x : T ⟶ M), (∀ i, Endomorphisms.Core.PreservesGroupLaw A (t.app (.op T) x i)) ↔
        ∃! y : T ⟶ E, y ≫ j = x) ∧
      ∃ e : yoneda.obj E ≅ ((Subfunctor.range t).preimage (Endomorphisms.Core.forgetGroupLaw A n)).toFunctor,
        e.hom ≫ ((Subfunctor.range t).preimage (Endomorphisms.Core.forgetGroupLaw A n)).ι ≫ Endomorphisms.Core.forgetGroupLaw A n =
          yoneda.map j ≫ t := by
  obtain ⟨E, j, hj, htest⟩ := Projective.EndomorphismEquations.Core.endomorphismTuples_closed_lifts A BA n t
  let : IsClosedImmersion j.left := hj
  let : Mono j := Over.mono_of_mono_left j
  let : Mono (Endomorphisms.Core.forgetGroupLaw A n) := forgetGroupLaw_mono A n
  refine ⟨E, j, hj, htest, ?_⟩
  apply RepresentedIntersectionTransfer.representedIntersectionTransfer t (Endomorphisms.Core.forgetGroupLaw A n) j
  intro T x
  rw [← preservesGroupLaws_iff_exists_endomorphismTuple]
  constructor
  · intro hx
    exact ((htest T x).mp hx).exists
  · rintro ⟨y, hy⟩
    exact (htest T x).mpr ⟨y, hy, fun z hz => (cancel_mono j).mp (hz.trans hy.symm)⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.NaturalEndomorphismClosedLocus.Core
