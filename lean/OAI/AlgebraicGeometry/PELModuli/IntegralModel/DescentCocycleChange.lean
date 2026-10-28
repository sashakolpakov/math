import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Descent

/-! # Descent Cocycle Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.DescentCocycleChange

noncomputable section

/-!
An ordinary normalized cocycle gives an effective finite descent relation.
In particular, symmetry and the equivalence relation are consequences of
the cocycle equations, rather than additional quotient assumptions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

namespace DescentCocycle

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {B T X : C} (u : T ⟶ B) (a : X ⟶ T)

abbrev overlap := pullback (a ≫ u) u
abbrev source : overlap u a ⟶ X := pullback.fst _ _
abbrev base : overlap u a ⟶ T := pullback.snd _ _

@[reassoc] theorem source_condition :
    source u a ≫ a ≫ u = base u a ≫ u := pullback.condition

def diagonal : X ⟶ overlap u a := pullback.lift (𝟙 X) a (by simp)

@[reassoc (attr := simp)] theorem diagonal_source :
    diagonal u a ≫ source u a = 𝟙 X := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem diagonal_base :
    diagonal u a ≫ base u a = a := pullback.lift_snd _ _ _

variable (t : overlap u a ⟶ X) (ht : t ≫ a = base u a)

def composition : pullback t (source u a) ⟶ overlap u a :=
  pullback.lift (pullback.fst _ _ ≫ source u a)
    (pullback.snd _ _ ≫ base u a) (by
      calc
        (pullback.fst _ _ ≫ source u a) ≫ (a ≫ u) =
            pullback.fst _ _ ≫ base u a ≫ u := by
          rw [Category.assoc, source_condition]
        _ = (pullback.fst _ _ ≫ t) ≫ a ≫ u := by
          rw [Category.assoc, ← Category.assoc t a u, ht]
        _ = (pullback.snd _ _ ≫ source u a) ≫ a ≫ u := by
          rw [pullback.condition]
        _ = (pullback.snd _ _ ≫ base u a) ≫ u := by
          simp only [Category.assoc, source_condition])

@[reassoc (attr := simp)] theorem composition_source :
    composition u a t ht ≫ source u a = pullback.fst _ _ ≫ source u a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem composition_base :
    composition u a t ht ≫ base u a = pullback.snd _ _ ≫ base u a :=
  pullback.lift_snd _ _ _

def reverse : overlap u a ⟶ overlap u a :=
  pullback.lift t (source u a ≫ a) (by
    rw [← Category.assoc, ht]
    simpa only [Category.assoc] using (source_condition u a).symm)

@[reassoc (attr := simp)] theorem reverse_source :
    reverse u a t ht ≫ source u a = t := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem reverse_base :
    reverse u a t ht ≫ base u a = source u a ≫ a := pullback.lift_snd _ _ _

/-- Normalization and the cocycle law force inverse transport. -/
theorem reverse_target (hnorm : diagonal u a ≫ t = 𝟙 X)
    (hcocycle : composition u a t ht ≫ t = pullback.snd _ _ ≫ t) :
    reverse u a t ht ≫ t = source u a := by
  let l : overlap u a ⟶ pullback t (source u a) :=
    pullback.lift (𝟙 _) (reverse u a t ht) (by simp)
  have hlfst : l ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _
  have hlsnd : l ≫ pullback.snd _ _ = reverse u a t ht := pullback.lift_snd _ _ _
  have hl : l ≫ composition u a t ht = source u a ≫ diagonal u a := by
    apply pullback.hom_ext
    · change (l ≫ composition u a t ht) ≫ source u a =
        (source u a ≫ diagonal u a) ≫ source u a
      rw [Category.assoc, composition_source, ← Category.assoc, hlfst,
        Category.id_comp, Category.assoc, diagonal_source, Category.comp_id]
    · change (l ≫ composition u a t ht) ≫ base u a =
        (source u a ≫ diagonal u a) ≫ base u a
      rw [Category.assoc, composition_base, ← Category.assoc, hlsnd,
        reverse_base, Category.assoc, diagonal_base]
  calc
    reverse u a t ht ≫ t = (l ≫ pullback.snd _ _) ≫ t := by rw [hlsnd]
    _ = l ≫ (composition u a t ht ≫ t) := by rw [hcocycle, Category.assoc]
    _ = (source u a ≫ diagonal u a) ≫ t := by rw [← Category.assoc, hl]
    _ = source u a := by rw [Category.assoc, hnorm, Category.comp_id]

/-- The actual overlap source and cocycle transport form an equivalence
relation; no quotient or effectiveness data enter this construction. -/
def equivalenceRelation (hnorm : diagonal u a ≫ t = 𝟙 X)
    (hcocycle : composition u a t ht ≫ t = pullback.snd _ _ ≫ t) :
    CategoryTheory.EquivalenceRelation (source u a) t where
  right_cancellation {Y} f g hs ht' := by
    apply pullback.hom_ext hs
    have h := congrArg (fun k => k ≫ a) ht'
    simpa only [Category.assoc, ht] using h
  r := diagonal u a
  reflexivity₁ := diagonal_source u a
  reflexivity₂ := hnorm
  s := reverse u a t ht
  symmetry₁ := reverse_source u a t ht
  symmetry₂ := reverse_target u a t ht hnorm hcocycle
  c := pullback.cone t (source u a)
  isLimit := pullback.isLimit t (source u a)
  t := composition u a t ht
  transitivity₁ := composition_source u a t ht
  transitivity₂ := hcocycle

end DescentCocycle

/-- The actual cartesian identification is an isomorphism of schemes over
the covering base. -/
def descentBaseChangeIso {B T X : Scheme.{u}} {u : T ⟶ B} {a : X ⟶ T}
    {Q : Over B} {q : X ⟶ Q.left} (h : IsPullback a q u Q.hom) :
    Over.mk a ≅ (Over.pullback u).obj Q :=
  Over.isoMk h.flip.isoPullback h.flip.isoPullback_hom_snd

/-- Normalized transport on the overlap of a finite faithfully flat cover
constructs a descended smooth proper geometrically connected scheme.
The quotient and its exact base-change identification are conclusions. -/
theorem effective_smooth_proper_cocycle_descent
    {K : Type u} [Field K] [Infinite K]
    {B T X : Scheme.{u}} (u : T ⟶ B)
    [IsFinite u] [Flat u] [Surjective u] [LocallyOfFinitePresentation u]
    (a : X ⟶ T) [Smooth a] [IsProper a] [GeometricallyConnected a]
    (t : DescentCocycle.overlap u a ⟶ X)
    (ht : t ≫ a = DescentCocycle.base u a)
    (hnorm : DescentCocycle.diagonal u a ≫ t = 𝟙 X)
    (hcocycle : DescentCocycle.composition u a t ht ≫ t =
      pullback.snd t (DescentCocycle.source u a) ≫ t)
    (n : ℕ) (i : X ⟶ ArithmeticGeometry.Models.SpreadingOut.Projective.Construction.ProjectiveConstruction.projectiveSpace (K := K) n)
    [IsClosedImmersion i] :
    ∃ (Q : Over B) (q : X ⟶ Q.left),
      IsPullback a q u Q.hom ∧
      Nonempty (Over.mk a ≅ (Over.pullback u).obj Q) ∧
      Smooth Q.hom ∧ IsProper Q.hom ∧ GeometricallyConnected Q.hom ∧
      IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧
      IsKernelPair q (DescentCocycle.source u a) t ∧
      ∀ (Y : Scheme.{u}) (f : X ⟶ Y),
        DescentCocycle.source u a ≫ f = t ≫ f →
        ∃! g : Q.left ⟶ Y, q ≫ g = f := by
  obtain ⟨Q, q, hcart, hfin, hflat, hfp, hsurj, hk, hdesc⟩ :=
    EffectiveFiniteDescent.effective_projective_finite_descent u a (DescentCocycle.base u a)
      (DescentCocycle.source u a) t (IsPullback.of_hasPullback (a ≫ u) u).flip ht
      (DescentCocycle.equivalenceRelation u a t ht hnorm hcocycle) n i
  have hs : Smooth Q.hom := MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hcart
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  exact ⟨Q, q, hcart, ⟨descentBaseChangeIso hcart⟩, hs,
    Descent.proper_of_faithfully_flat_cartesian hcart,
    ArithmeticGeometry.Models.SpreadingOut.GeometricDescent.Construction.geometricallyConnected_of_surjective_cartesian hcart.flip,
    hfin, hflat, hfp, hsurj, hk, hdesc⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.DescentCocycleChange
