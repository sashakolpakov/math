import OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Proper Cycle Linearity -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

noncomputable section

section

/-!
# ProjectionFormula: geometric cycle operations and their relations on Chow groups

Proper pushforward uses the image of each generic point and its native residue
field degree, followed by extraction of the requested codimension. Infinite
residue-field extensions have degree zero. The graph construction intersects
the graph cycle with the exterior product of the source fundamental cycle and
the input cycle, then pushes to the source.

The quotient-level operations are their actual geometric relations. They do
not choose an arbitrary value before proving the moving and descent theorems.
ProjectionFormula's repaired target includes totality and uniqueness of these relations as
well as the projection formula, so the relation interface adds no hypotheses
on the input Chow classes and cannot make the target vacuous.

No theorem stub or axiom-declared Chow operation is imported.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

/-- Every morphism between the projective presentations is proper. -/
theorem morphism_isProper {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) : IsProper f.left := by
  have hsep : IsSeparated Y.structureMap :=
    @IsProper.toIsSeparated _ _ _ Y.projective.isProper
  have hcomp : IsProper (f.left ≫ Y.structureMap) := f.w.symm ▸ X.projective.isProper
  exact @IsProper.of_comp X.carrier Y.carrier Foundations.Scheme.ProjectiveSpace.complexBase f.left Y.structureMap hcomp hsep

/-- The closed irreducible support with generic point the image generic point. -/
def imageSupport {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (A : IrreducibleCloseds X.carrier) :
    IrreducibleCloseds Y.carrier :=
  irreducibleSetEquivPoints.symm (f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A))

/-- Properness identifies the constructed support with the actual closed image. -/
theorem imageSupport_eq_image {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (A : IrreducibleCloseds X.carrier) :
    (imageSupport f A : Set Y.carrier) = f.left '' (A : Set X.carrier) := by
  let φ : X.carrier ⟶ Y.carrier := f.left
  let : IsProper φ := morphism_isProper f
  change closure {φ (CycleClass.Thom.IntersectionGeometry.supportPoint A)} = _
  have h := φ.isClosedMap.closure_image_eq_of_continuous
    φ.continuous {CycleClass.Thom.IntersectionGeometry.supportPoint A}
  rw [Set.image_singleton] at h
  have hA : closure {CycleClass.Thom.IntersectionGeometry.supportPoint A} = (A : Set X.carrier) :=
    congrArg (fun W : IrreducibleCloseds X.carrier => (W : Set X.carrier))
      (irreducibleSetEquivPoints.symm_apply_apply A)
  rw [hA] at h
  exact h

@[simp]
theorem imageSupport_id (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A : IrreducibleCloseds X.carrier) : imageSupport (𝟙 X.toOver) A = A :=
  irreducibleSetEquivPoints.symm_apply_apply A

/-- The requested graded component of the usual proper pushforward of a support. -/
def cyclePushforwardGenerator {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (p q : ℕ) (A : X.DimensionCycleSupport p) :
    Y.RationalDimensionCycle q :=
  (f.left.residueDegree (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) : ℚ) •
    CycleClass.Thom.IntersectionGeometry.supportInDegree Y q (imageSupport f A.val)

/-- Proper pushforward, extended linearly from actual generic supports. -/
def cyclePushforward {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (p q : ℕ) :
    X.RationalDimensionCycle p →ₗ[ℚ] Y.RationalDimensionCycle q :=
  Finsupp.linearCombination ℚ (cyclePushforwardGenerator f p q)

theorem cyclePushforward_single {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (p q : ℕ)
    (A : X.DimensionCycleSupport p) (r : ℚ) :
    cyclePushforward f p q (Finsupp.single A r) =
      r • cyclePushforwardGenerator f p q A :=
  Finsupp.linearCombination_single ℚ _ _

/-- The coefficient is exactly the residue degree on the image support. -/
theorem cyclePushforwardGenerator_apply {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (p q : ℕ)
    (A : X.DimensionCycleSupport p) (B : Y.DimensionCycleSupport q) :
    cyclePushforwardGenerator f p q A B =
      if imageSupport f A.val = B.val then
        (f.left.residueDegree (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) : ℚ) else 0 := by
  classical
  simp only [cyclePushforwardGenerator, Finsupp.smul_apply,
    CycleClass.Thom.IntersectionGeometry.supportInDegree_apply, smul_eq_mul]
  split_ifs <;> simp

theorem cyclePushforwardGenerator_of_residueDegree_zero
    {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
    (p q : ℕ) (A : X.DimensionCycleSupport p)
    (h : f.left.residueDegree (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = 0) :
    cyclePushforwardGenerator f p q A = 0 := by
  change (f.left.residueDegree (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) : ℚ) •
    CycleClass.Thom.IntersectionGeometry.supportInDegree Y q (imageSupport f A.val) = 0
  rw [h, Nat.cast_zero, zero_smul]

theorem cyclePushforward_id (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) :
    cyclePushforward (𝟙 X.toOver) p p = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro A r
  simp only [cyclePushforward, Finsupp.linearCombination_single,
    cyclePushforwardGenerator, imageSupport_id]
  change r • ((AlgebraicGeometry.Scheme.Hom.residueDegree
    (𝟙 X.carrier) (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) : ℚ) •
      CycleClass.Thom.IntersectionGeometry.supportInDegree X p A.val) = Finsupp.single A r
  rw [Scheme.Hom.residueDegree_id]
  simp only [Nat.cast_one, one_smul, CycleClass.Thom.IntersectionGeometry.supportInDegree, dite_eq_left A.property]
  exact Finsupp.smul_single_one A r

/-- The fundamental cycle of the whole reduced smooth scheme. -/
def fundamentalCycle (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    X.RationalDimensionCycle 0 := CycleClass.Thom.IntersectionGeometry.reducedClosedCycle X 0 ⊤

/-- A choice of smooth projective presentation of the actual product. -/
structure ProductPresentation (X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) where
  space : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation
  fst : space.toOver ⟶ X.toOver
  snd : space.toOver ⟶ Y.toOver
  isLimit : IsLimit (BinaryFan.mk fst snd)

namespace ProductPresentation

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProductPresentation X Y)

/-- The graph is constructed by the product universal property. -/
def graph (f : X.toOver ⟶ Y.toOver) : X.toOver ⟶ P.space.toOver :=
  BinaryFan.IsLimit.lift P.isLimit (𝟙 X.toOver) f

@[simp, reassoc]
theorem graph_fst (f : X.toOver ⟶ Y.toOver) : P.graph f ≫ P.fst = 𝟙 X.toOver :=
  BinaryFan.IsLimit.lift_fst P.isLimit _ _

@[simp, reassoc]
theorem graph_snd (f : X.toOver ⟶ Y.toOver) : P.graph f ≫ P.snd = f :=
  BinaryFan.IsLimit.lift_snd P.isLimit _ _

theorem graph_unique (f : X.toOver ⟶ Y.toOver) (g : X.toOver ⟶ P.space.toOver)
    (hfst : g ≫ P.fst = 𝟙 X.toOver) (hsnd : g ≫ P.snd = f) : g = P.graph f := by
  apply BinaryFan.IsLimit.hom_ext P.isLimit
  · exact hfst.trans (P.graph_fst f).symm
  · exact hsnd.trans (P.graph_snd f).symm

/-- The graph cycle, in codimension equal to the target dimension. -/
def graphCycle (f : X.toOver ⟶ Y.toOver) (n : ℕ) :
    P.space.RationalDimensionCycle n :=
  cyclePushforward (P.graph f) 0 n (fundamentalCycle X)

/-- Flat pullback through the second product projection: `[X] × a`. -/
def secondPullbackCycle (p : ℕ) (a : Y.RationalDimensionCycle p) :
    P.space.RationalDimensionCycle p :=
  cast (congrArg P.space.RationalDimensionCycle (Nat.zero_add p))
    (CycleClass.Thom.IntersectionGeometry.exteriorCycleProduct X Y P.space P.fst P.snd P.isLimit 0 p
      (fundamentalCycle X) a)

/-- The graph-intersection construction, followed by proper first projection.
Only principal divisors and local intersection multiplicities enter the relation. -/
def RepresentsPullback (f : X.toOver ⟶ Y.toOver) (n p : ℕ)
    (a : Y.RationalDimensionCycle p) (b : X.RationalDimensionCycle p) : Prop :=
  ∃ c : P.space.RationalDimensionCycle (n + p),
    CycleClass.Thom.IntersectionGeometry.RepresentsIntersection P.space n p (P.graphCycle f n)
      (P.secondPullbackCycle p a) c ∧
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p b (cyclePushforward P.fst (n + p) p c)

theorem representsPullback_of_intersection
    (f : X.toOver ⟶ Y.toOver) (n p : ℕ)
    (a : Y.RationalDimensionCycle p) (c : P.space.RationalDimensionCycle (n + p))
    (hc : CycleClass.Thom.IntersectionGeometry.RepresentsIntersection P.space n p (P.graphCycle f n)
      (P.secondPullbackCycle p a) c) :
    P.RepresentsPullback f n p a (cyclePushforward P.fst (n + p) p c) :=
  ⟨c, hc, CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X p _⟩

end ProductPresentation

/-- ThomClass's Chow quotient by explicitly specified principal-divisor relations. -/
abbrev ChowQ (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) := CycleClass.Thom.IntersectionGeometry.ChowQ X p

def cycleToChowQ (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) :
    X.RationalDimensionCycle p →ₗ[ℚ] ChowQ X p :=
  (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p).mkQ

theorem cycleToChowQ_surjective (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) :
    Function.Surjective (cycleToChowQ X p) := Submodule.mkQ_surjective _

theorem cycleToChowQ_eq_iff (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (a b : X.RationalDimensionCycle p) :
    cycleToChowQ X p a = cycleToChowQ X p b ↔ CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p a b :=
  (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_iff_chow_eq X p a b).symm

/-- Changing any representative by a principal-divisor relation preserves the
geometric intersection relation. This uses its definition, not the projection formula. -/
theorem representsIntersection_congr (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    {a a' : X.RationalDimensionCycle p} {b b' : X.RationalDimensionCycle q}
    {c c' : X.RationalDimensionCycle (p + q)}
    (ha : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p a a')
    (hb : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X q b b')
    (hc : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (p + q) c c') :
    CycleClass.Thom.IntersectionGeometry.RepresentsIntersection X p q a b c ↔
      CycleClass.Thom.IntersectionGeometry.RepresentsIntersection X p q a' b' c' := by
  constructor
  · rintro ⟨u, v, w, hau, hbv, huv, hcw⟩
    exact ⟨u, v, w,
      CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X p (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_symm X p ha) hau,
      CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X q (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_symm X q hb) hbv,
      huv,
      CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X (p + q)
        (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_symm X (p + q) hc) hcw⟩
  · rintro ⟨u, v, w, hau, hbv, huv, hcw⟩
    exact ⟨u, v, w, CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X p ha hau,
      CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X q hb hbv, huv,
      CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X (p + q) hc hcw⟩

/-- The actual relation induced by proper pushforward on cycle representatives. -/
def chowPushforward {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (p q : ℕ) (a : ChowQ X p) : Set (ChowQ Y q) :=
  {b | ∃ z : X.RationalDimensionCycle p,
    cycleToChowQ X p z = a ∧ cycleToChowQ Y q (cyclePushforward f p q z) = b}

/-- The geometric intersection relation on the actual Chow quotients. -/
def chowIntersection (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (a : ChowQ X p) (b : ChowQ X q) : Set (ChowQ X (p + q)) :=
  {c | ∃ (z : X.RationalDimensionCycle p) (w : X.RationalDimensionCycle q)
      (v : X.RationalDimensionCycle (p + q)),
    cycleToChowQ X p z = a ∧ cycleToChowQ X q w = b ∧
    cycleToChowQ X (p + q) v = c ∧ CycleClass.Thom.IntersectionGeometry.RepresentsIntersection X p q z w v}

/-- The geometric graph pullback relation on the actual Chow quotients. -/
def chowPullback {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (P : ProductPresentation X Y) (f : X.toOver ⟶ Y.toOver) (n p : ℕ)
    (a : ChowQ Y p) : Set (ChowQ X p) :=
  {b | ∃ (z : Y.RationalDimensionCycle p) (w : X.RationalDimensionCycle p),
    cycleToChowQ Y p z = a ∧ cycleToChowQ X p w = b ∧
    P.RepresentsPullback f n p z w}

/-- On actual cycle representatives the quotient relation is precisely ThomClass's
geometric intersection relation; taking the quotient adds no possible outputs. -/
theorem chowIntersection_mk_iff (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (c : X.RationalDimensionCycle (p + q)) :
    cycleToChowQ X (p + q) c ∈
        chowIntersection X p q (cycleToChowQ X p a) (cycleToChowQ X q b) ↔
      CycleClass.Thom.IntersectionGeometry.RepresentsIntersection X p q a b c := by
  constructor
  · rintro ⟨u, v, w, hu, hv, hw, h⟩
    exact (representsIntersection_congr X p q
      ((cycleToChowQ_eq_iff X p u a).mp hu)
      ((cycleToChowQ_eq_iff X q v b).mp hv)
      ((cycleToChowQ_eq_iff X (p + q) w c).mp hw)).mp h
  · intro h
    exact ⟨a, b, c, rfl, rfl, rfl, h⟩

/-- The actual quotient map once preservation of principal-divisor relations
has been proved. This helper does not assume the projection formula, and the
repaired target supplies no descent premise. -/
def descendedPushforward {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (p q : ℕ)
    (h : CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p ≤
      (CycleClass.Thom.IntersectionGeometry.rationalEquivalences Y q).comap (cyclePushforward f p q)) :
    ChowQ X p →ₗ[ℚ] ChowQ Y q :=
  (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p).mapQ (CycleClass.Thom.IntersectionGeometry.rationalEquivalences Y q)
    (cyclePushforward f p q) h

@[simp]
theorem descendedPushforward_mk {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (p q : ℕ)
    (h : CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p ≤
      (CycleClass.Thom.IntersectionGeometry.rationalEquivalences Y q).comap (cyclePushforward f p q))
    (z : X.RationalDimensionCycle p) :
    descendedPushforward f p q h (cycleToChowQ X p z) =
      cycleToChowQ Y q (cyclePushforward f p q z) := rfl

theorem chowPushforward_eq_singleton_of_descent
    {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) (p q : ℕ)
    (h : CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p ≤
      (CycleClass.Thom.IntersectionGeometry.rationalEquivalences Y q).comap (cyclePushforward f p q))
    (a : ChowQ X p) :
    chowPushforward f p q a = {descendedPushforward f p q h a} := by
  ext b
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Set.mem_singleton_iff, ← hz, descendedPushforward_mk]
  · intro hb
    obtain rfl := Set.mem_singleton_iff.mp hb
    obtain ⟨z, rfl⟩ := cycleToChowQ_surjective X p a
    exact ⟨z, rfl, rfl⟩

/-- Precisely the remaining geometric descent statement: the pushforward
relation is the graph of a linear map iff actual principal divisors map to
rational equivalences. Neither side contains the projection formula. -/
theorem chowPushforward_map_exists_iff
    {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) (p q : ℕ) :
    (∃ F : ChowQ X p →ₗ[ℚ] ChowQ Y q,
      ∀ a, chowPushforward f p q a = {F a}) ↔
    ∀ z : X.RationalDimensionCycle p, CycleClass.Thom.IntersectionGeometry.IsPrincipalDivisor X p z →
      cyclePushforward f p q z ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences Y q := by
  constructor
  · rintro ⟨F, hF⟩ z hz
    have hz0 : cycleToChowQ X p z = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span hz)
    have hm : cycleToChowQ Y q (cyclePushforward f p q z) ∈
        chowPushforward f p q 0 := ⟨z, hz0, rfl⟩
    rw [hF, map_zero, Set.mem_singleton_iff] at hm
    exact (Submodule.Quotient.mk_eq_zero _).mp hm
  · intro h
    have hd : CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p ≤
        (CycleClass.Thom.IntersectionGeometry.rationalEquivalences Y q).comap (cyclePushforward f p q) :=
      Submodule.span_le.mpr h
    exact ⟨descendedPushforward f p q hd,
      chowPushforward_eq_singleton_of_descent f p q hd⟩

theorem chowPushforward_nonempty {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (p q : ℕ) (a : ChowQ X p) :
    (chowPushforward f p q a).Nonempty := by
  obtain ⟨z, rfl⟩ := cycleToChowQ_surjective X p a
  exact ⟨_, z, rfl, rfl⟩

theorem chowPushforward_id (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (a : ChowQ X p) : chowPushforward (𝟙 X.toOver) p p a = {a} := by
  ext b
  constructor
  · rintro ⟨z, hz, hb⟩
    rw [cyclePushforward_id, LinearMap.id_apply] at hb
    exact hb.symm.trans hz
  · intro hb
    obtain rfl := Set.mem_singleton_iff.mp hb
    obtain ⟨z, rfl⟩ := cycleToChowQ_surjective X p b
    refine ⟨z, rfl, ?_⟩
    rw [cyclePushforward_id, LinearMap.id_apply]

end

/-! Proper meeting is preserved under linear combinations in the second input. -/

open _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry

theorem add_right (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ) (a : X.RationalDimensionCycle p)
    (b c : X.RationalDimensionCycle q) (hb : CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a b) (hc : CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a c) :
    CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a (b + c) := by
  intro D hD A hA
  rcases Finset.mem_union.mp (Finsupp.support_add hA) with hA | hA
  · exact hb D hD A hA
  · exact hc D hD A hA

theorem sub_right (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ) (a : X.RationalDimensionCycle p)
    (b c : X.RationalDimensionCycle q) (hb : CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a b) (hc : CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a c) :
    CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a (b - c) := by
  intro D hD A hA
  rcases Finset.mem_union.mp (Finsupp.support_sub hA) with hA | hA
  · exact hb D hD A hA
  · exact hc D hD A hA

theorem smul_right (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ) (a : X.RationalDimensionCycle p)
    (b : X.RationalDimensionCycle q) (r : ℚ) (hb : CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a b) :
    CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a (r • b) :=
  fun D hD A hA => hb D hD A (Finsupp.support_smul hA)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity
