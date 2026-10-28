import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NaturalGraphOpen
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.GraphTupleRepresentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.GraphTupleRecovery
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RepresentedIntersectionTransfer

/-! # Natural Hom Open -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.NaturalHomOpen.Core

noncomputable section

/-! For any monic natural Hilbert parameter family, its actual graph
open represents precisely the morphism tuples whose graphs occur in that family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (X Y : Over S) (n : ℕ)
variable [Flat X.hom] [IsProper X.hom] [LocallyOfFinitePresentation X.hom]
variable [IsSeparated Y.hom]
variable {B : Over S} [IsLocallyNoetherian B.left] [LocallyOfFiniteType B.hom]

theorem naturalHilbert_homOpen
    (t : yoneda.obj B ⟶ Has.Core.hilbertTuples X Y n) [Mono t] :
    ∃ (M : Over S) (j : M ⟶ B), IsOpenImmersion j.left ∧ LocallyOfFiniteType M.hom ∧
      (∀ (T : Over S) (a : T ⟶ B),
        Has.Core.IsGraphTuple X Y n (t.app (.op T) a) ↔ ∃! b : T ⟶ M, b ≫ j = a) ∧
      ∃ e : yoneda.obj M ≅ ((Subfunctor.range t).preimage (Has.Core.graphs X Y n)).toFunctor,
        e.hom ≫ ((Subfunctor.range t).preimage (Has.Core.graphs X Y n)).ι ≫ Has.Core.graphs X Y n =
          yoneda.map j ≫ t := by
  let F : Fin n → Hilbert.Functor.Family (X ⨯ Y) B := t.app (.op B) (𝟙 B)
  let M := Intrinsic.GraphTupleOpen.Hom.nativeGraphTupleOver X Y F
  let j : M ⟶ B := Intrinsic.GraphTupleOpen.Hom.nativeGraphTupleInclusion X Y F
  let : Mono j := Intrinsic.GraphTupleOpen.Hom.nativeGraphTupleInclusion_mono X Y F
  have h (T : Over S) (a : T ⟶ B) :
      Has.Core.IsGraphTuple X Y n (t.app (.op T) a) ↔ ∃! b : T ⟶ M, b ≫ j = a := by
    rw [NaturalGraphOpen.Hom.naturalHilbertTuple_eq_pullback]
    exact Intrinsic.GraphTupleOpen.Hom.nativeGraphTupleOpen_iff_unique_lift X Y F a
  refine ⟨M, j, Intrinsic.GraphTupleOpen.Hom.nativeGraphTupleInclusion_isOpenImmersion X Y F,
    Intrinsic.GraphTupleRepresentation.Hom.nativeGraphTupleOver_locallyOfFiniteType X Y F, h, ?_⟩
  let : Mono (Has.Core.graphs X Y n) := GraphTupleRecovery.Core.graphTuples_mono X Y n
  apply RepresentedIntersectionTransfer.representedIntersectionTransfer t (Has.Core.graphs X Y n) j
  intro T a
  constructor
  · rintro ⟨v, hv⟩
    have hg : Has.Core.IsGraphTuple X Y n (t.app (.op T) a) :=
      hv ▸ GraphTupleRecovery.Core.graphTuples_isGraphTuple X Y n v
    exact ((h T a).mp hg).exists
  · rintro ⟨b, hb⟩
    have hg := (h T a).mpr ⟨b, hb, fun c hc => (cancel_mono j).mp (hc.trans hb.symm)⟩
    exact ((GraphTupleRecovery.Core.isGraphTuple_iff_existsUnique_morphismTuple X Y n _).mp hg).exists

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.NaturalHomOpen.Core
