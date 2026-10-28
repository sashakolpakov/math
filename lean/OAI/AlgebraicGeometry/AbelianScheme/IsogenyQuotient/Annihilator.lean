import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupRepresentable

/-! # Annihilator -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Annihilator.Construction

noncomputable section

/-!
The relative annihilator of a subgroup for an actual scheme pairing.
The all-test-scheme definition ensures arbitrary base-change compatibility.
In the etale case its geometric model is obtained by a clopen agreement
locus; representability of the annihilator is not part of the definition.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A B W : Over S}
  [GrpObj A] [GrpObj B] [GrpObj W]

/-- A bilinear pairing of group schemes, with its genuine scheme map. -/
structure SchemeBicharacter where
  hom : A ⊗ B ⟶ W
  one_left : ∀ (X : Over S) (y : X ⟶ B), lift (1 : X ⟶ A) y ≫ hom = 1
  one_right : ∀ (X : Over S) (x : X ⟶ A), lift x (1 : X ⟶ B) ≫ hom = 1
  mul_left : ∀ (X : Over S) (x z : X ⟶ A) (y : X ⟶ B),
    lift (x * z) y ≫ hom = (lift x y ≫ hom) * (lift z y ≫ hom)
  mul_right : ∀ (X : Over S) (x : X ⟶ A) (y z : X ⟶ B),
    lift x (y * z) ≫ hom = (lift x y ≫ hom) * (lift x z ≫ hom)

namespace SchemeBicharacter

variable (e : SchemeBicharacter (A := A) (B := B) (W := W))

def pairValue {X : Over S} (x : X ⟶ A) (y : X ⟶ B) : X ⟶ W :=
  lift x y ≫ e.hom

theorem pairValue_natural {X Y : Over S} (f : X ⟶ Y) (x : Y ⟶ A) (y : Y ⟶ B) :
    e.pairValue (f ≫ x) (f ≫ y) = f ≫ e.pairValue x y := by
  simp only [SchemeBicharacter.pairValue, ← Category.assoc, comp_lift]

def pairRightHom {X : Over S} (x : X ⟶ A) : (X ⟶ B) →* (X ⟶ W) where
  toFun := e.pairValue x
  map_one' := e.one_right X x
  map_mul' := e.mul_right X x

variable {P : Over S} (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)

/-- Annihilation is tested after every map of test schemes. -/
def relativeAnnihilator : TorsionQuotient.SubgroupFunctor.RelativeSubgroup B P where
  points X t := {
    carrier := {y | ∀ (Y : Over S) (f : Y ⟶ X) (x : Y ⟶ A),
      x ∈ F.points Y (f ≫ t) → e.pairValue x (f ≫ y) = 1}
    one_mem' := by
      intro Y f x _
      rw [MonObj.comp_one]
      exact e.one_right Y x
    mul_mem' := by
      intro y z hy hz Y f x hx
      rw [MonObj.comp_mul]
      change e.pairRightHom x ((f ≫ y) * (f ≫ z)) = 1
      rw [map_mul]
      change e.pairValue x (f ≫ y) * e.pairValue x (f ≫ z) = 1
      rw [hy Y f x hx, hz Y f x hx, one_mul]
    inv_mem' := by
      intro y hy Y f x hx
      rw [GrpObj.comp_inv]
      change e.pairRightHom x (f ≫ y)⁻¹ = 1
      rw [map_inv]
      change (e.pairValue x (f ≫ y))⁻¹ = 1
      rw [hy Y f x hx, inv_one] }
  naturality := by
    intro X Y f t y hy Z g x hx
    exact hy Z (g ≫ f) x (by simpa only [Category.assoc] using hx)

/-- Annihilators commute with arbitrary change of parameter scheme. -/
theorem relativeAnnihilator_baseChange {T : Over S} (b : T ⟶ P) :
    (e.relativeAnnihilator F).baseChange b = e.relativeAnnihilator (F.baseChange b) := by
  ext X t y
  change (∀ (Y : Over S) (f : Y ⟶ X) (x : Y ⟶ A),
    x ∈ F.points Y (f ≫ (t ≫ b)) → _) ↔
    (∀ (Y : Over S) (f : Y ⟶ X) (x : Y ⟶ A),
    x ∈ F.points Y ((f ≫ t) ≫ b) → _)
  simp only [Category.assoc]

/-- Universal evaluation on the product of the subgroup model and the
opposite block. Its vanishing cuts out the annihilator. -/
def annihilatorEvaluation (R : F.Model) : R.carrier ⊗ B ⟶ W :=
  e.pairValue (fst R.carrier B ≫ R.toGroup) (snd R.carrier B)

def annihilatorProjection (R : F.Model) : R.carrier ⊗ B ⟶ P ⊗ B :=
  R.toBase ⊗ₘ 𝟙 B

set_option backward.isDefEq.respectTransparency false in
theorem annihilator_iff_evaluation
    (R : F.Model) {T : Over S} (t : T ⟶ P) (y : T ⟶ B) :
    y ∈ (e.relativeAnnihilator F).points T t ↔
      pullback.fst (annihilatorProjection F R) (lift t y) ≫
        e.annihilatorEvaluation F R = 1 := by
  let p := annihilatorProjection (B := B) F R
  let b := lift t y
  let D := pullback p b
  let l : D ⟶ R.carrier ⊗ B := pullback.fst p b
  let r : D ⟶ T := pullback.snd p b
  have hbase : l ≫ fst R.carrier B ≫ R.toBase = r ≫ t := by
    have h := congrArg (fun z => z ≫ fst P B) (pullback.condition (f := p) (g := b))
    simp only [Category.assoc] at h
    rw [show p ≫ fst P B = fst R.carrier B ≫ R.toBase from tensorHom_fst _ _,
      show b ≫ fst P B = t from lift_fst _ _] at h
    exact h
  have hgroup : l ≫ snd R.carrier B = r ≫ y := by
    have h := congrArg (fun z => z ≫ snd P B) (pullback.condition (f := p) (g := b))
    simp only [Category.assoc] at h
    rw [show p ≫ snd P B = snd R.carrier B from
      (tensorHom_snd _ _).trans (Category.comp_id _),
      show b ≫ snd P B = y from lift_snd _ _] at h
    exact h
  constructor
  · intro hy
    have hx : l ≫ fst R.carrier B ≫ R.toGroup ∈ F.points D (r ≫ t) := by
      apply (R.points_iff D (r ≫ t) _).mpr
      exact ⟨l ≫ fst R.carrier B, by simpa only [Category.assoc] using hbase,
        Category.assoc _ _ _⟩
    have h := hy D r _ hx
    change l ≫ e.pairValue (fst R.carrier B ≫ R.toGroup) (snd R.carrier B) = 1
    rw [← e.pairValue_natural, hgroup]
    exact h
  · intro h Y f x hx
    change pullback.fst p b ≫ e.annihilatorEvaluation F R = 1 at h
    obtain ⟨a, hat, hax⟩ := (R.points_iff Y (f ≫ t) x).mp hx
    let k : Y ⟶ R.carrier ⊗ B := lift a (f ≫ y)
    have hk : k ≫ p = f ≫ b := by
      apply hom_ext
      · simpa only [k, p, b, annihilatorProjection, Category.assoc,
          tensorHom_fst, lift_fst_assoc, lift_fst] using hat
      · simp only [k, p, b, annihilatorProjection, Category.assoc,
          tensorHom_snd, Category.comp_id, lift_snd]
    have h' := congrArg (fun z => pullback.lift k f hk ≫ z) h
    simp only [← Category.assoc, pullback.lift_fst, MonObj.comp_one] at h'
    change k ≫ e.pairValue (fst R.carrier B ≫ R.toGroup) (snd R.carrier B) = 1 at h'
    rw [← e.pairValue_natural] at h'
    simpa only [k, lift_fst_assoc, lift_snd, hax] using h'

set_option backward.isDefEq.respectTransparency false in
omit [GrpObj B] in
theorem annihilatorProjection_isPullback (R : F.Model) :
    IsPullback (fst R.carrier B) (annihilatorProjection (B := B) F R)
      R.toBase (fst P B) where
  w := by simp only [annihilatorProjection, tensorHom_fst]
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun c => by
    refine ⟨lift c.fst (c.snd ≫ snd P B), ?_, ?_, ?_⟩
    · exact lift_fst _ _
    · change lift c.fst (c.snd ≫ snd P B) ≫ (R.toBase ⊗ₘ 𝟙 B) = c.snd
      apply hom_ext
      · simpa only [annihilatorProjection, Category.assoc,
          tensorHom_fst, lift_fst_assoc] using c.condition
      · simp only [Category.assoc, tensorHom_snd,
          Category.comp_id, lift_snd]
    · intro m h₁ h₂
      change m ≫ fst R.carrier B = c.fst at h₁
      change m ≫ (R.toBase ⊗ₘ 𝟙 B) = c.snd at h₂
      apply hom_ext
      · simpa only [lift_fst] using h₁
      · have h := congrArg (fun z => z ≫ snd P B) h₂
        simpa only [annihilatorProjection, Category.assoc,
          tensorHom_snd, Category.comp_id, lift_snd] using h)⟩

/-- Annihilation cuts out a clopen, finite etale locus in the opposite
block over the parameter scheme. This proves the geometric condition
under arbitrary base change, rather than only on geometric fibers. -/
theorem finite_etale_annihilator_locus
    (R : F.Model) [Etale R.toBase.left]
    [Etale W.hom] [IsSeparated W.hom] :
    ∃ U : (P ⊗ B).left.Opens,
      IsFinite U.ι ∧ Etale U.ι ∧
      ∀ (T : Over S) (t : T ⟶ P) (y : T ⟶ B),
        (∀ x : T.left, (lift t y).left x ∈ U) ↔
          y ∈ (e.relativeAnnihilator F).points T t := by
  have : IsFinite (annihilatorProjection (B := B) F R).left :=
    MorphismProperty.of_isPullback
      ((annihilatorProjection_isPullback (B := B) F R).map (Over.forget S)) R.finite
  have : Etale (annihilatorProjection (B := B) F R).left :=
    MorphismProperty.of_isPullback
      ((annihilatorProjection_isPullback (B := B) F R).map (Over.forget S))
      (inferInstanceAs (Etale R.toBase.left))
  obtain ⟨U, hfinite, hetale, hU⟩ := AgreementLocus.Construction.finite_etale_agreement_locus
    (annihilatorProjection (B := B) F R) (e.annihilatorEvaluation F R) 1
  refine ⟨U, hfinite, hetale, ?_⟩
  intro T t y
  have hUT := hU T (lift t y)
  rw [MonObj.comp_one] at hUT
  exact hUT.trans (e.annihilator_iff_evaluation F R t y).symm

set_option backward.isDefEq.respectTransparency false in
/-- Build the annihilator's finite locally free model from its clopen
locus. Both the model and its embedding are constructed explicitly. -/
def relativeAnnihilator_model_from_locus
    [IsFinite B.hom] [Etale B.hom]
    (U : (P ⊗ B).left.Opens) [IsFinite U.ι]
    (hU : ∀ (T : Over S) (t : T ⟶ P) (y : T ⟶ B),
      (∀ x : T.left, (lift t y).left x ∈ U) ↔
        y ∈ (e.relativeAnnihilator F).points T t) :
    (e.relativeAnnihilator F).Model := by
  let Q := SubgroupRepresentable.Construction.openParameter (P ⊗ B) U
  let j : Q ⟶ P ⊗ B := SubgroupRepresentable.Construction.openParameterι (P ⊗ B) U
  have : IsFinite j.left := inferInstanceAs (IsFinite U.ι)
  have : Etale j.left := inferInstanceAs (Etale U.ι)
  have : Mono j.left := inferInstanceAs (Mono U.ι)
  have : Mono j := Over.mono_of_mono_left j
  have : IsFinite (fst P B).left :=
    inferInstanceAs (IsFinite (pullback.fst P.hom B.hom))
  have : Etale (fst P B).left :=
    inferInstanceAs (Etale (pullback.fst P.hom B.hom))
  refine {
    carrier := Q
    toBase := j ≫ fst P B
    toGroup := j ≫ snd P B
    finite := ?_
    flat := ?_
    finitePresentation := ?_
    jointly_monic := ?_
    points_iff := ?_ }
  · change IsFinite (j.left ≫ (fst P B).left)
    infer_instance
  · change Flat (j.left ≫ (fst P B).left)
    infer_instance
  · change LocallyOfFinitePresentation (j.left ≫ (fst P B).left)
    infer_instance
  · intro X a b hbase hgroup
    apply (cancel_mono j).mp
    apply hom_ext
    · simpa only [Category.assoc] using hbase
    · simpa only [Category.assoc] using hgroup
  · intro X t y
    constructor
    · intro hy
      have hrange : Set.range (lift t y).left ⊆ Set.range U.ι := by
        rw [Scheme.Opens.range_ι, Set.range_subset_iff]
        exact (hU X t y).mpr hy
      let l := IsOpenImmersion.lift U.ι (lift t y).left hrange
      have hl : l ≫ U.ι = (lift t y).left := IsOpenImmersion.lift_fac _ _ hrange
      have hlbase : l ≫ Q.hom = X.hom := by
        change l ≫ (U.ι ≫ (P ⊗ B).hom) = X.hom
        rw [← Category.assoc, hl, (lift t y).w]
      let a : X ⟶ Q := Over.homMk l hlbase
      have ha : a ≫ j = lift t y := Over.OverMorphism.ext hl
      exact ⟨a, by rw [← Category.assoc, ha, lift_fst],
        by rw [← Category.assoc, ha, lift_snd]⟩
    · rintro ⟨a, hat, hay⟩
      have ha : a ≫ j = lift t y := by
        apply hom_ext
        · simpa only [Category.assoc, lift_fst] using hat
        · simpa only [Category.assoc, lift_snd] using hay
      apply (hU X t y).mp
      intro x
      rw [← ha]
      exact (a.left x).property

/-- The annihilator of a finite etale subgroup in a finite etale block
has an actual finite locally free geometric model. -/
theorem relativeAnnihilator_has_model
    (R : F.Model) [Etale R.toBase.left]
    [Etale W.hom] [IsSeparated W.hom] [IsFinite B.hom] [Etale B.hom] :
    Nonempty (e.relativeAnnihilator F).Model := by
  obtain ⟨U, hfinite, _, hU⟩ := e.finite_etale_annihilator_locus F R
  have : IsFinite U.ι := hfinite
  exact ⟨e.relativeAnnihilator_model_from_locus F U hU⟩

end SchemeBicharacter

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Annihilator.Construction
