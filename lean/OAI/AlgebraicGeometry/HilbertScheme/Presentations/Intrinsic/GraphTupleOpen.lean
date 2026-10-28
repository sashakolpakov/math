import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.FamilyGraphOpen
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.OverOpenFactorization
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Has

/-! # Graph Tuple Open -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.GraphTupleOpen.Hom

noncomputable section

/-! Finite tuples of native Hilbert families have an actual open graph
locus satisfying the statement's graph predicate on every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (X Y : Over S) [IsProper X.hom]
variable {n : ℕ} {B : Over S} (F : Fin n → Hilbert.Functor.Family (X ⨯ Y) B)

def nativeGraphTupleOpen : B.left.Opens := ⨅ i, FamilyGraphOpen.Hom.nativeFamilyGraphOpen X Y (F i)

theorem mem_nativeGraphTupleOpen (b : B.left) :
    b ∈ nativeGraphTupleOpen X Y F ↔ ∀ i, b ∈ FamilyGraphOpen.Hom.nativeFamilyGraphOpen X Y (F i) := by
  change b ∈ ((⨅ i, FamilyGraphOpen.Hom.nativeFamilyGraphOpen X Y (F i) : B.left.Opens) : Set B.left) ↔ _
  rw [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  rfl

theorem nativeGraphTupleOpen_baseChange_iff_range [IsLocallyNoetherian B.left]
    {T : Over S} (a : T ⟶ B) :
    Has.Core.IsGraphTuple X Y n (fun i => Hilbert.Functor.pullbackFamily (X ⨯ Y) a (F i)) ↔
      Set.range a.left ⊆ (nativeGraphTupleOpen X Y F : Set B.left) := by
  have hi (i : Fin n) :
      IsIso ((Hilbert.Functor.pullbackFamily (X ⨯ Y) a (F i)).val.subschemeι ≫
        (HomFunctor.Hom.graphProjection X Y T).left) ↔
      Set.range a.left ⊆ (FamilyGraphOpen.Hom.nativeFamilyGraphOpen X Y (F i) : Set B.left) :=
    (isIso_iff_of_reflects_iso
      (GraphLocus.Hom.subschemeProjection X Y (Hilbert.Functor.pullbackFamily (X ⨯ Y) a (F i)).val)
      (Over.forget S)).trans (FamilyGraphOpen.Hom.nativeFamilyGraphOpen_baseChange_iff_range X Y (F i) a)
  change (∀ i, _) ↔ _
  simp_rw [hi]
  constructor
  · intro h b hb
    exact (mem_nativeGraphTupleOpen X Y F b).mpr (fun i => h i hb)
  · intro h i b hb
    exact (mem_nativeGraphTupleOpen X Y F b).mp (h hb) i

def nativeGraphTupleOver : Over S := OverOpenFactorization.openOver B (nativeGraphTupleOpen X Y F)

def nativeGraphTupleInclusion : nativeGraphTupleOver X Y F ⟶ B :=
  OverOpenFactorization.openOverInclusion B (nativeGraphTupleOpen X Y F)

instance nativeGraphTupleInclusion_isOpenImmersion :
    IsOpenImmersion (nativeGraphTupleInclusion X Y F).left :=
  inferInstanceAs (IsOpenImmersion (OverOpenFactorization.openOverInclusion B (nativeGraphTupleOpen X Y F)).left)

instance nativeGraphTupleInclusion_mono : Mono (nativeGraphTupleInclusion X Y F) :=
  Over.mono_of_mono_left _

theorem nativeGraphTupleOpen_iff_unique_lift [IsLocallyNoetherian B.left]
    {T : Over S} (a : T ⟶ B) :
    Has.Core.IsGraphTuple X Y n (fun i => Hilbert.Functor.pullbackFamily (X ⨯ Y) a (F i)) ↔
      ∃! b : T ⟶ nativeGraphTupleOver X Y F, b ≫ nativeGraphTupleInclusion X Y F = a :=
  (nativeGraphTupleOpen_baseChange_iff_range X Y F a).trans
    (OverOpenFactorization.range_subset_open_iff_unique_over_lift B (nativeGraphTupleOpen X Y F) a)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.GraphTupleOpen.Hom
