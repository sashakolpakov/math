import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.IncidenceChoice

/-! # Generic -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.Generic

noncomputable section

section

/-! Coordinate choices for the source and all support base loci,
with independent images under finitely many surjective first-order maps. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace BaseJetLinearChoice

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearCut

theorem values_cons {n k : ℕ} (a : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) (L : Fin k → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) :
    (fun b => (Fin.cons (α := fun _ => Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) a L b).val) =
      Fin.cons a.val (fun b => (L b).val) := by
  funext b
  exact Fin.cases rfl (fun _ => rfl) b

theorem exists_form (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m l : ℕ) (hl : l < m + 1)
    (L : Fin l → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    {τ ι : Type} [Finite τ] [Finite ι] (H : τ → IrreducibleCloseds X.carrier)
    (D : ι → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1 →ₗ[ℂ] (Fin (m + 1) → ℂ))
    (hD : ∀ j, Function.Surjective (D j))
    (hLI : ∀ j, LinearIndependent ℂ (fun a => D j (L a))) :
    ∃ a : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1,
      (∀ C : irreducibleComponents (Projective.LinearCut.commonZero X.embedding (fun b => (L b).val)),
        a.val ∉ (X.embedding (CycleClass.Thom.IntersectionGeometry.supportPoint (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier
          (Projective.LinearCut.commonZero X.embedding (fun b => (L b).val)) C))).asHomogeneousIdeal) ∧
      (∀ t, ∀ C : irreducibleComponents (Support.PairBase.factor X (H t) L),
        a.val ∉ ((CycleClass.Geometric.GenericPoint.reducedSupportι (H t) ≫ X.embedding) (CycleClass.Thom.IntersectionGeometry.supportPoint
          (CycleClass.Thom.IntersectionGeometry.closedComponentSupport (CycleClass.Geometric.GenericPoint.reducedSupportScheme (H t)) (Support.PairBase.factor X (H t) L) C))).asHomogeneousIdeal) ∧
      ∀ j, D j a ∉ Submodule.span ℂ (Set.range (fun b => D j (L b))) := by
  classical
  let S := Projective.LinearCut.commonZero X.embedding (fun b => (L b).val)
  let : NoetherianSpace S := NoetherianSpace.set (S : Set X.carrier)
  let : Finite (irreducibleComponents S) :=
    (NoetherianSpace.finite_irreducibleComponents (α := S)).to_subtype
  let B t := Support.PairBase.factor X (H t) L
  let (t : τ) : NoetherianSpace (B t) := NoetherianSpace.set (B t : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme (H t)))
  let (t : τ) : Finite (irreducibleComponents (B t)) :=
    (NoetherianSpace.finite_irreducibleComponents (α := B t)).to_subtype
  let z : irreducibleComponents S ⊕ (Σ t : τ, irreducibleComponents (B t)) →
      Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension := Sum.elim
    (fun C => X.embedding (CycleClass.Thom.IntersectionGeometry.supportPoint (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S C)))
    (fun b => (CycleClass.Geometric.GenericPoint.reducedSupportι (H b.1) ≫ X.embedding)
      (CycleClass.Thom.IntersectionGeometry.supportPoint (CycleClass.Thom.IntersectionGeometry.closedComponentSupport (CycleClass.Geometric.GenericPoint.reducedSupportScheme (H b.1)) (B b.1) b.2)))
  let N j := (Submodule.span ℂ (Set.range (fun b => D j (L b)))).comap (D j)
  have hN : ∀ j, N j ≠ ⊤ :=
    fun j => IndependentLinearCut.comap_span_ne_top X m D hD hl L hLI j
  obtain ⟨a, ha, haN⟩ := ConstrainedLinearForms.exists_form X.ambientDimension z N hN
  exact ⟨a, fun C => ha (Sum.inl C), fun t C => ha (Sum.inr ⟨t, C⟩), fun j => haN j⟩

end BaseJetLinearChoice

end

section

/-! Explicit stage bounds used in the generic-projection induction. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace InductionBounds

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearCut OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Pair

def source (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {l : ℕ}
    (L : Fin l → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) : Prop :=
  ∀ C : IrreducibleCloseds X.carrier,
    (C : Set X.carrier) ⊆ Projective.LinearCut.commonZero X.embedding (fun i => (L i).val) → l ≤ X.supportCodimension C

def factor (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W : IrreducibleCloseds X.carrier) {l : ℕ}
    (L : Fin l → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) : Prop :=
  ∀ C : IrreducibleCloseds (CycleClass.Geometric.GenericPoint.reducedSupportScheme W),
    (C : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) ⊆ Support.PairBase.factor X W L →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension C (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap) + l ≤
        Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap

def incidence (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W Z : IrreducibleCloseds X.carrier) {k : ℕ}
    (L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) : Prop :=
  ∀ C : IrreducibleCloseds (Support.Pair.space X W Z),
    (C : Set (Support.Pair.space X W Z)) ⊆ Support.PairIncidenceStep.incidence X W Z k L →
    ¬ (C : Set (Support.Pair.space X W Z)) ⊆ Support.PairIncidenceStep.diagonal X W Z →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension C (Support.Pair.base X W Z) + k ≤
        Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap + Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.structureMap

theorem source_empty (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) : source X Fin.elim0 :=
  fun _ _ => Nat.zero_le _

theorem factor_empty (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W : IrreducibleCloseds X.carrier) :
    factor X W Fin.elim0 := by
  intro C _
  exact Foundations.Scheme.SupportDimension.supportTranscendenceDimension_le C (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap)

theorem source_cons (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] {l : ℕ}
    (L : Fin l → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) (hL : source X L)
    (a : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    (ha : ∀ C : irreducibleComponents (Projective.LinearCut.commonZero X.embedding (fun b => (L b).val)),
      a.val ∉ (X.embedding (CycleClass.Thom.IntersectionGeometry.supportPoint (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier
        (Projective.LinearCut.commonZero X.embedding (fun b => (L b).val)) C))).asHomogeneousIdeal) :
    source X (Fin.cons a L) :=
  IndependentLinearCut.codimension_cons X m l L hL a ha

theorem factor_cons (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W : IrreducibleCloseds X.carrier) {l : ℕ}
    (L : Fin l → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) (hL : factor X W L)
    (a : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    (ha : ∀ C : irreducibleComponents (Support.PairBase.factor X W L),
      a.val ∉ ((CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.embedding) (CycleClass.Thom.IntersectionGeometry.supportPoint
        (CycleClass.Thom.IntersectionGeometry.closedComponentSupport (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) (Support.PairBase.factor X W L) C))).asHomogeneousIdeal) :
    factor X W (Fin.cons a L) := by
  unfold factor Support.PairBase.factor
  rw [BaseJetLinearChoice.values_cons]
  exact LinearCutDimension.cons (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap) (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.embedding)
    (fun b => (L b).val) (Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap) hL a.val ha

theorem incidence_zero (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W Z : IrreducibleCloseds X.carrier)
    (L : Fin 1 → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) : incidence X W Z L :=
  fun C _ _ => Support.Pair.dimension X W Z C

theorem independent_cons {A B : Type} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (D : A →ₗ[ℂ] B) {l : ℕ} (L : Fin l → A)
    (hL : LinearIndependent ℂ (fun b => D (L b))) (a : A)
    (ha : D a ∉ Submodule.span ℂ (Set.range (fun b => D (L b)))) :
    LinearIndependent ℂ (fun b => D (Fin.cons (α := fun _ => A) a L b)) := by
  have he : (fun b => D (Fin.cons (α := fun _ => A) a L b)) = Fin.cons (D a) (fun b => D (L b)) := by
    funext b
    exact Fin.cases rfl (fun _ => rfl) b
  rw [he, linearIndependent_finCons]
  exact ⟨hL, ha⟩

end InductionBounds

end

section

/-! A single tuple of linear forms satisfies all support-pair incidence
bounds and all prescribed independent first-order conditions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Forms

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.Generic.InductionBounds OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearCut OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
  [SmoothOfRelativeDimension m X.structureMap]
  {τ ι : Type} [Finite τ] [Finite ι] (W Z : τ → IrreducibleCloseds X.carrier)
  (D : ι → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1 →ₗ[ℂ] (Fin (m + 1) → ℂ))
  (hD : ∀ j, Function.Surjective (D j))

include hD in
theorem exists_partial (k : ℕ) (hk : k ≤ m) :
    ∃ L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1,
      InductionBounds.source X L ∧ (∀ t, InductionBounds.factor X (W t) L) ∧ (∀ t, InductionBounds.factor X (Z t) L) ∧
      (∀ t, InductionBounds.incidence X (W t) (Z t) L) ∧
      ∀ j, LinearIndependent ℂ (fun a => D j (L a)) := by
  induction k with
  | zero =>
    obtain ⟨a, haX, haWZ, haD⟩ := BaseJetLinearChoice.exists_form X m 0
      (Nat.zero_lt_succ m) Fin.elim0 (Sum.elim W Z) D hD
      (fun _ => linearIndependent_empty_type)
    refine ⟨Fin.cons a Fin.elim0, InductionBounds.source_cons X m Fin.elim0 (InductionBounds.source_empty X) a haX,
      ?_, ?_, fun t => InductionBounds.incidence_zero X (W t) (Z t) _, ?_⟩
    · exact fun t => InductionBounds.factor_cons X (W t) Fin.elim0 (InductionBounds.factor_empty X (W t)) a (haWZ (Sum.inl t))
    · exact fun t => InductionBounds.factor_cons X (Z t) Fin.elim0 (InductionBounds.factor_empty X (Z t)) a (haWZ (Sum.inr t))
    · exact fun j => InductionBounds.independent_cons (D j) Fin.elim0 linearIndependent_empty_type a (haD j)
  | succ k ih =>
    obtain ⟨L, hX, hW, hZ, hI, hLI⟩ := ih (by omega)
    obtain ⟨a, haX, haW, haZ, haD, haI⟩ :=
      IncidenceChoice.exists_form X m k (by omega) L W Z D hD hLI
    refine ⟨Fin.cons a L, InductionBounds.source_cons X m L hX a haX,
      fun t => InductionBounds.factor_cons X (W t) L (hW t) a (haW t),
      fun t => InductionBounds.factor_cons X (Z t) L (hZ t) a (haZ t), ?_,
      fun j => InductionBounds.independent_cons (D j) L (hLI j) a (haD j)⟩
    intro t
    exact Support.PairIncidenceStep.step X (W t) (Z t) k
      (Foundations.Scheme.SupportDimension.supportTranscendenceDimension (W t) X.structureMap)
      (Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Z t) X.structureMap) L (hW t) (hZ t) (hI t) a (haI t)

include hD in
theorem exists_forms :
    ∃ L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1,
      (∀ x : X.carrier, ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal) ∧
      (∀ t, InductionBounds.incidence X (W t) (Z t) L) ∧
      ∀ j, LinearIndependent ℂ (fun a => D j (L a)) := by
  obtain ⟨L, hX, _, _, hI, hLI⟩ := exists_partial X m W Z D hD m le_rfl
  refine ⟨L, ?_, hI, hLI⟩
  intro x
  by_contra hn
  push Not at hn
  let C : IrreducibleCloseds X.carrier := irreducibleSetEquivPoints.symm x
  have hx : CycleClass.Thom.IntersectionGeometry.supportPoint C = x := irreducibleSetEquivPoints.apply_symm_apply x
  have hC : (C : Set X.carrier) ⊆ Projective.LinearCut.commonZero X.embedding (fun a => (L a).val) := by
    apply (Supports.supportPoint_mem_iff_subset _ C).mp
    rw [hx]
    exact (Projective.LinearCut.mem_commonZero X.embedding (fun a => (L a).val) x).mpr hn
  have hb := hX C hC
  have hd := Grading.supportDimension_add_codimension X m C
  omega

end Forms

end

/-! Generic linear projections of any target dimension, defined on
prescribed low-dimensional supports. The surrounding projective scheme
may have larger dimension and retain a projection center. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace OnSupports

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.Generic.InductionBounds

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (r : ℕ)
  {τ ι : Type} [Finite τ] [Finite ι] (W Z : τ → IrreducibleCloseds X.carrier)
  (D : ι → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1 →ₗ[ℂ] (Fin (r + 1) → ℂ))
  (hD : ∀ j, Function.Surjective (D j))

include hD in
theorem exists_partial (k : ℕ) (hk : k ≤ r) :
    ∃ L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1,
      (∀ t, InductionBounds.factor X (W t) L) ∧ (∀ t, InductionBounds.factor X (Z t) L) ∧
      (∀ t, InductionBounds.incidence X (W t) (Z t) L) ∧
      ∀ j, LinearIndependent ℂ (fun a => D j (L a)) := by
  induction k with
  | zero =>
    obtain ⟨a, _, haWZ, haD⟩ := BaseJetLinearChoice.exists_form X r 0
      (Nat.zero_lt_succ r) Fin.elim0 (Sum.elim W Z) D hD
      (fun _ => linearIndependent_empty_type)
    refine ⟨Fin.cons a Fin.elim0, ?_, ?_, fun t => InductionBounds.incidence_zero X (W t) (Z t) _, ?_⟩
    · exact fun t => InductionBounds.factor_cons X (W t) Fin.elim0 (InductionBounds.factor_empty X (W t)) a (haWZ (Sum.inl t))
    · exact fun t => InductionBounds.factor_cons X (Z t) Fin.elim0 (InductionBounds.factor_empty X (Z t)) a (haWZ (Sum.inr t))
    · exact fun j => InductionBounds.independent_cons (D j) Fin.elim0 linearIndependent_empty_type a (haD j)
  | succ k ih =>
    obtain ⟨L, hW, hZ, hI, hLI⟩ := ih (by omega)
    obtain ⟨a, _, haW, haZ, haD, haI⟩ :=
      IncidenceChoice.exists_form X r k (by omega) L W Z D hD hLI
    refine ⟨Fin.cons a L,
      fun t => InductionBounds.factor_cons X (W t) L (hW t) a (haW t),
      fun t => InductionBounds.factor_cons X (Z t) L (hZ t) a (haZ t), ?_,
      fun j => InductionBounds.independent_cons (D j) L (hLI j) a (haD j)⟩
    intro t
    exact Support.PairIncidenceStep.step X (W t) (Z t) k
      (Foundations.Scheme.SupportDimension.supportTranscendenceDimension (W t) X.structureMap)
      (Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Z t) X.structureMap) L (hW t) (hZ t) (hI t) a (haI t)

theorem factor_no_base (H : IrreducibleCloseds X.carrier)
    (L : Fin (r + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    (hH : Foundations.Scheme.SupportDimension.supportTranscendenceDimension H X.structureMap ≤ r) (hL : InductionBounds.factor X H L)
    (x : X.carrier) (hx : x ∈ (H : Set X.carrier)) :
    ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal := by
  by_contra hn
  push Not at hn
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage H x hx
  let C : IrreducibleCloseds (CycleClass.Geometric.GenericPoint.reducedSupportScheme H) := irreducibleSetEquivPoints.symm y
  have hC : (C : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme H)) ⊆ Support.PairBase.factor X H L := by
    apply (Supports.supportPoint_mem_iff_subset _ C).mp
    have hp : CycleClass.Thom.IntersectionGeometry.supportPoint C = y := irreducibleSetEquivPoints.apply_symm_apply y
    rw [hp]
    apply (Projective.LinearCut.mem_commonZero _ _ _).mpr
    intro a
    change (L a).val ∈ (X.embedding (CycleClass.Geometric.GenericPoint.reducedSupportι H y)).asHomogeneousIdeal
    rw [CycleClass.Thom.IntersectionGeometry.supportPreimage_spec]
    exact hn a
  have hb := hL C hC
  omega

include hD in
theorem exists_forms {κ : Type} [Finite κ] (H : κ → IrreducibleCloseds X.carrier)
    (hH : ∀ t, Foundations.Scheme.SupportDimension.supportTranscendenceDimension (H t) X.structureMap ≤ r) :
    ∃ L : Fin (r + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1,
      (∀ t, InductionBounds.factor X (W t) L) ∧ (∀ t, InductionBounds.factor X (Z t) L) ∧
      (∀ t, InductionBounds.incidence X (W t) (Z t) L) ∧
      (∀ t, ∀ x ∈ (H t : Set X.carrier), ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal) ∧
      ∀ j, LinearIndependent ℂ (fun a => D j (L a)) := by
  obtain ⟨L, hW, hZ, hI, hLI⟩ := exists_partial X r (Sum.elim W H) (Sum.elim Z H) D hD r le_rfl
  exact ⟨L, fun t => hW (Sum.inl t), fun t => hZ (Sum.inl t), fun t => hI (Sum.inl t),
    fun t x hx => factor_no_base X r (H t) L (hH t) (hW (Sum.inr t)) x hx, hLI⟩

end OnSupports

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.Generic
