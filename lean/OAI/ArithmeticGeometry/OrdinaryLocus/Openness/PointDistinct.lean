import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Point Distinct -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PointDistinct.Construction

noncomputable section

section

/-! Open loci distinguishing geometric points, for the Openness counting argument. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

/-- A map from a reduced scheme factors through a closed immersion when
its underlying image is contained in that closed subscheme. -/
theorem exists_lift_of_range_subset_closedImmersion
    {T X Y : Scheme} (i : X ⟶ Y) (h : T ⟶ Y)
    [IsClosedImmersion i] [IsReduced T]
    (himage : Set.range h ⊆ Set.range i) :
    ∃ l : T ⟶ X, l ≫ i = h := by
  have : Surjective (pullback.snd i h) := ⟨fun t => by
    obtain ⟨x, hx⟩ := himage ⟨t, rfl⟩
    obtain ⟨z, _, hz⟩ := Scheme.Pullback.exists_preimage_pullback x t hx
    exact ⟨z, hz⟩⟩
  have : IsIso (pullback.snd i h) :=
    isIso_of_isClosedImmersion_of_surjective (pullback.snd i h)
  refine ⟨inv (pullback.snd i h) ≫ pullback.fst i h, ?_⟩
  rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

variable {S : Scheme} {X Y : Over S} [IsSeparated Y.hom]

/-- A reduced test scheme whose image lies in the equalizer actually
equalizes the two morphisms. -/
theorem comp_eq_of_range_subset_equalizer
    (f g : X ⟶ Y) {T : Over S} [IsReduced T.left] (h : T ⟶ X)
    (himage : Set.range h.left ⊆ Set.range (equalizer.ι f g).left) :
    h ≫ f = h ≫ g := by
  obtain ⟨l, hl⟩ := exists_lift_of_range_subset_closedImmersion
    (equalizer.ι f g).left h.left himage
  apply Over.OverMorphism.ext
  change h.left ≫ f.left = h.left ≫ g.left
  rw [← hl, Category.assoc, Category.assoc]
  exact congrArg (l ≫ ·) (congrArg (fun k => k.left) (equalizer.condition f g))

/-- The open complement of the equalizer of two maps to a separated scheme. -/
def distinctLocus (f g : X ⟶ Y) : X.left.Opens :=
  ⟨(Set.range (equalizer.ι f g).left)ᶜ,
    (equalizer.ι f g).left.isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- On a reduced one-point test scheme, membership in the complement of
the equalizer means the two induced points are distinct. -/
theorem mem_distinctLocus_iff
    (f g : X ⟶ Y) {T : Over S} [IsReduced T.left] [Subsingleton T.left]
    (h : T ⟶ X) (t : T.left) :
    h.left t ∈ distinctLocus f g ↔ h ≫ f ≠ h ≫ g := by
  constructor
  · intro ht heq
    apply ht
    refine ⟨(equalizer.lift h heq).left t, ?_⟩
    exact congrArg (fun k : T ⟶ X => k.left t) (equalizer.lift_ι h heq)
  · intro hne ht
    apply hne
    apply comp_eq_of_range_subset_equalizer f g h
    rintro _ ⟨t', rfl⟩
    simpa only [Subsingleton.elim t' t] using ht

end

section

/-! Finite tuples in a scheme over a base, for the Openness counting argument. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S : Scheme} (A : Over S)

/-- The iterated fiber product representing ordered tuples of points. -/
def pointTuple : ℕ → Over S
  | 0 => Over.mk (𝟙 S)
  | n + 1 => Over.mk
      (pullback.fst (pointTuple n).hom A.hom ≫ (pointTuple n).hom)

def pointTupleHead (n : ℕ) : Construction.pointTuple A (n + 1) ⟶ A :=
  Over.homMk (pullback.snd (Construction.pointTuple A n).hom A.hom) pullback.condition.symm

def pointTupleTail (n : ℕ) : Construction.pointTuple A (n + 1) ⟶ Construction.pointTuple A n :=
  Over.homMk (pullback.fst (Construction.pointTuple A n).hom A.hom)

/-- Coordinate projection from an ordered tuple. -/
def pointTupleProjection : (n : ℕ) → Fin n → (Construction.pointTuple A n ⟶ A)
  | 0, i => Fin.elim0 i
  | n + 1, i => Fin.cases (pointTupleHead A n)
      (fun j => pointTupleTail A n ≫ pointTupleProjection n j) i

/-- Assemble an ordered family into its representing fiber product. -/
def pointTupleLift {T : Over S} : (n : ℕ) → (Fin n → (T ⟶ A)) → (T ⟶ Construction.pointTuple A n)
  | 0, _ => Over.homMk T.hom
  | n + 1, v => Over.homMk
      (pullback.lift (pointTupleLift n (fun i => v i.succ)).left (v 0).left
        (by simp)) (by
      change pullback.lift _ _ _ ≫
        (pullback.fst (Construction.pointTuple A n).hom A.hom ≫ (Construction.pointTuple A n).hom) = T.hom
      rw [pullback.lift_fst_assoc]
      exact (pointTupleLift n (fun i => v i.succ)).w)

@[simp]
theorem pointTupleLift_projection {T : Over S} (n : ℕ) (v : Fin n → (T ⟶ A))
    (i : Fin n) : Construction.pointTupleLift A n v ≫ Construction.pointTupleProjection A n i = v i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · apply Over.OverMorphism.ext
      exact pullback.lift_snd _ _ _
    · change Construction.pointTupleLift A (n + 1) v ≫
          (pointTupleTail A n ≫ Construction.pointTupleProjection A n j) = v j.succ
      rw [← Category.assoc]
      have ht : Construction.pointTupleLift A (n + 1) v ≫ pointTupleTail A n =
          Construction.pointTupleLift A n (fun i => v i.succ) := by
        apply Over.OverMorphism.ext
        exact pullback.lift_fst _ _ _
      rw [ht]
      exact ih (fun i => v i.succ) j

instance pointTuple_flat [Flat A.hom] (n : ℕ) : Flat (Construction.pointTuple A n).hom := by
  induction n with
  | zero => change Flat (𝟙 S); infer_instance
  | succ n ih =>
    have := ih
    change Flat (pullback.fst (Construction.pointTuple A n).hom A.hom ≫ (Construction.pointTuple A n).hom)
    infer_instance

instance pointTuple_locallyOfFinitePresentation [LocallyOfFinitePresentation A.hom]
    (n : ℕ) : LocallyOfFinitePresentation (Construction.pointTuple A n).hom := by
  induction n with
  | zero => change LocallyOfFinitePresentation (𝟙 S); infer_instance
  | succ n ih =>
    have := ih
    change LocallyOfFinitePresentation
      (pullback.fst (Construction.pointTuple A n).hom A.hom ≫ (Construction.pointTuple A n).hom)
    infer_instance

end

/-! Schemes of ordered distinct points for the Openness counting argument. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S : Scheme} (A : Over S) [IsSeparated A.hom]

/-- The open locus of tuples whose coordinates are pairwise distinct. -/
def pointConfigurationOpen (n : ℕ) : (Construction.pointTuple A n).left.Opens :=
  ⟨{x | ∀ i j : Fin n, i ≠ j →
      x ∈ distinctLocus (Construction.pointTupleProjection A n i) (Construction.pointTupleProjection A n j)}, by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_iInter_of_finite fun _ => (distinctLocus _ _).isOpen⟩

/-- The scheme representing ordered distinct geometric points. -/
def pointConfiguration (n : ℕ) : Over S :=
  Over.mk ((pointConfigurationOpen A n).ι ≫ (Construction.pointTuple A n).hom)

def pointConfigurationInclusion (n : ℕ) : pointConfiguration A n ⟶ Construction.pointTuple A n :=
  Over.homMk (pointConfigurationOpen A n).ι

instance pointConfiguration_flat [Flat A.hom] (n : ℕ) :
    Flat (pointConfiguration A n).hom := by
  change Flat ((pointConfigurationOpen A n).ι ≫ (Construction.pointTuple A n).hom)
  infer_instance

instance pointConfiguration_locallyOfFinitePresentation [LocallyOfFinitePresentation A.hom]
    (n : ℕ) : LocallyOfFinitePresentation (pointConfiguration A n).hom := by
  change LocallyOfFinitePresentation
    ((pointConfigurationOpen A n).ι ≫ (Construction.pointTuple A n).hom)
  infer_instance

/-- A point of the configuration scheme is exactly the existence of an
injective ordered family, on a reduced one-point test scheme. -/
theorem nonempty_pointConfiguration_iff
    {T : Over S} [IsReduced T.left] [Subsingleton T.left] [Nonempty T.left] (n : ℕ) :
    Nonempty (T ⟶ pointConfiguration A n) ↔
      ∃ v : Fin n → (T ⟶ A), Function.Injective v := by
  let t : T.left := Classical.choice inferInstance
  constructor
  · rintro ⟨h⟩
    let h' := h ≫ pointConfigurationInclusion A n
    refine ⟨fun i => h' ≫ Construction.pointTupleProjection A n i, ?_⟩
    intro i j hij
    by_contra hne
    have hmem : h'.left t ∈ pointConfigurationOpen A n := (h.left t).property
    have hdistinct := hmem i j hne
    exact ((mem_distinctLocus_iff _ _ h' t).mp hdistinct) hij
  · rintro ⟨v, hv⟩
    let h := Construction.pointTupleLift A n v
    have himage : Set.range h.left ⊆ Set.range (pointConfigurationOpen A n).ι := by
      rintro _ ⟨t', rfl⟩
      rw [Scheme.Opens.range_ι]
      intro i j hne
      apply (mem_distinctLocus_iff _ _ h t').mpr
      simpa only [h, pointTupleLift_projection] using fun heq => hne (hv heq)
    let l := IsOpenImmersion.lift (pointConfigurationOpen A n).ι h.left himage
    refine ⟨Over.homMk l ?_⟩
    change l ≫ ((pointConfigurationOpen A n).ι ≫ (Construction.pointTuple A n).hom) = T.hom
    rw [← Category.assoc, IsOpenImmersion.lift_fac]
    exact h.w

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PointDistinct.Construction
