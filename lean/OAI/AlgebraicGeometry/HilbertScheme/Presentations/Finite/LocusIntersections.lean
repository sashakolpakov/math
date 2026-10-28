import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SubfunctorRepresentations
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-! # Locus Intersections -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.LocusIntersections

noncomputable section

/-! Finite intersections of already constructed quasi-compact immersion loci
are represented by their actual fiber products. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v
variable {S : Scheme.{u}} {M : Over S}

theorem immersionRepresentable_inf {F G : Subfunctor (yoneda.obj M)}
    (hF : SubfunctorRepresentations.ImmersionRepresentable F) (hG : SubfunctorRepresentations.ImmersionRepresentable G) :
    SubfunctorRepresentations.ImmersionRepresentable (F ⊓ G) := by
  obtain ⟨Z, j, hj, hjc, eF, heF⟩ := hF
  obtain ⟨W, k, hk, hkc, eG, heG⟩ := hG
  let := hj
  let := hjc
  let := hk
  let := hkc
  let V := pullback j k
  let a : V ⟶ Z := pullback.fst j k
  let b : V ⟶ W := pullback.snd j k
  let l : V ⟶ M := a ≫ j
  have hp : IsPullback a.left b.left j.left k.left :=
    (IsPullback.of_hasPullback j k).map (Over.forget S)
  have : IsImmersion a.left := MorphismProperty.of_isPullback hp.flip hk
  have : QuasiCompact a.left := MorphismProperty.of_isPullback hp.flip hkc
  have hl : IsImmersion l.left := inferInstanceAs (IsImmersion (a.left ≫ j.left))
  have hlc : QuasiCompact l.left := inferInstanceAs (QuasiCompact (a.left ≫ j.left))
  let := hl
  have : Mono l := Over.mono_of_mono_left l
  refine ⟨V, l, hl, hlc, SubfunctorRepresentations.subfunctor_representation_of_lifts (F ⊓ G) l ?_⟩
  intro T x
  change (x ∈ F.obj (.op T) ∧ x ∈ G.obj (.op T)) ↔ _
  rw [SubfunctorRepresentations.represented_subfunctor_mem F j eF heF T x, SubfunctorRepresentations.represented_subfunctor_mem G k eG heG T x]
  constructor
  · rintro ⟨⟨f, hf⟩, ⟨g, hg⟩⟩
    let v : T ⟶ V := pullback.lift f g (hf.trans hg.symm)
    refine ⟨v, ?_⟩
    change pullback.lift f g (hf.trans hg.symm) ≫ pullback.fst j k ≫ j = x
    rw [pullback.lift_fst_assoc, hf]
  · rintro ⟨v, hv⟩
    refine ⟨⟨v ≫ a, (Category.assoc _ _ _).trans hv⟩, ⟨v ≫ b, ?_⟩⟩
    rw [Category.assoc]
    change v ≫ (pullback.snd j k ≫ k) = x
    rw [← pullback.condition]
    exact hv

theorem immersionRepresentable_top : SubfunctorRepresentations.ImmersionRepresentable (⊤ : Subfunctor (yoneda.obj M)) := by
  refine ⟨M, 𝟙 M, ?_, ?_, SubfunctorRepresentations.subfunctor_representation_of_lifts ⊤ (𝟙 M) ?_⟩
  · change IsImmersion (𝟙 M.left)
    infer_instance
  · change QuasiCompact (𝟙 M.left)
    infer_instance
  · intro T x
    exact ⟨fun _ => ⟨x, Category.comp_id x⟩, fun _ => Set.mem_univ x⟩

theorem immersionRepresentable_finset_inf {κ : Type v} (s : Finset κ)
    (F : κ → Subfunctor (yoneda.obj M)) (hF : ∀ i ∈ s, SubfunctorRepresentations.ImmersionRepresentable (F i)) :
    SubfunctorRepresentations.ImmersionRepresentable (⨅ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (immersionRepresentable_top (M := M))
  | @insert a s ha ih =>
    rw [Finset.iInf_insert]
    exact immersionRepresentable_inf (hF a (Finset.mem_insert_self a s))
      (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.LocusIntersections
