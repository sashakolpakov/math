import Mathlib.CategoryTheory.EquivalenceRelation

/-! # Groupoid Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupoidIs.Construction.Groupoid

/-!
# Cartesian composition squares for an internal equivalence relation

Composition of arrows in an equivalence relation is a base change of either
endpoint map. These squares supply the two base changes of the relation algebra
needed by the invariant-polynomial and invariant-basis arguments for FiniteDescent.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] {R U : C} {s t : R ⟶ U}

/-- Compose a compatible pair of arrows in the internal relation. -/
noncomputable def compose (e : CategoryTheory.EquivalenceRelation s t)
    {T : C} (a b : T ⟶ R) (h : a ≫ t = b ≫ s) : T ⟶ R :=
  PullbackCone.IsLimit.lift e.isLimit a b h ≫ e.t

@[reassoc (attr := simp)]
theorem compose_source (e : CategoryTheory.EquivalenceRelation s t)
    {T : C} (a b : T ⟶ R) (h : a ≫ t = b ≫ s) :
    compose e a b h ≫ s = a ≫ s := by
  simp [compose, Category.assoc, e.transitivity₁]

@[reassoc (attr := simp)]
theorem compose_target (e : CategoryTheory.EquivalenceRelation s t)
    {T : C} (a b : T ⟶ R) (h : a ≫ t = b ≫ s) :
    compose e a b h ≫ t = b ≫ t := by
  simp [compose, Category.assoc, e.transitivity₂]

/-- Recover composable arrows from a composite and its first arrow. -/
noncomputable def sourceLift (e : CategoryTheory.EquivalenceRelation s t)
    {T : C} (a b : T ⟶ R) (h : a ≫ s = b ≫ s) : T ⟶ e.c.pt :=
  PullbackCone.IsLimit.lift e.isLimit b
    (compose e (b ≫ e.s) a (by simpa only [Category.assoc, e.symmetry₂] using h.symm))
    (by simp [e.symmetry₁])

@[reassoc (attr := simp)]
theorem sourceLift_first (e : CategoryTheory.EquivalenceRelation s t)
    {T : C} (a b : T ⟶ R) (h : a ≫ s = b ≫ s) :
    sourceLift e a b h ≫ e.c.fst = b := by
  simp [sourceLift]

@[reassoc (attr := simp)]
theorem sourceLift_composite (e : CategoryTheory.EquivalenceRelation s t)
    {T : C} (a b : T ⟶ R) (h : a ≫ s = b ≫ s) :
    sourceLift e a b h ≫ e.t = a := by
  apply e.right_cancellation
  · simpa [Category.assoc, e.transitivity₁] using h.symm
  · simp [sourceLift, Category.assoc, e.transitivity₂]

/-- The first arrow and the composite determine the composable pair. -/
theorem sourceLift_unique (e : CategoryTheory.EquivalenceRelation s t)
    {T : C} (a b : T ⟶ R) (h : a ≫ s = b ≫ s)
    (m : T ⟶ e.c.pt) (hm : m ≫ e.t = a) (hmf : m ≫ e.c.fst = b) :
    m = sourceLift e a b h := by
  apply PullbackCone.IsLimit.hom_ext e.isLimit
  · simpa using hmf
  · apply e.right_cancellation
    · calc
        (m ≫ e.c.snd) ≫ s = (m ≫ e.c.fst) ≫ t := by
          simpa only [Category.assoc] using congrArg (fun f => m ≫ f) e.c.condition.symm
        _ = b ≫ t := by rw [hmf]
        _ = (sourceLift e a b h ≫ e.c.snd) ≫ s := by
          simp [sourceLift, Category.assoc, e.symmetry₁]
    · calc
        (m ≫ e.c.snd) ≫ t = (m ≫ e.t) ≫ t := by
          simp only [Category.assoc, e.transitivity₂]
        _ = a ≫ t := by rw [hm]
        _ = (sourceLift e a b h ≫ e.c.snd) ≫ t := by
          simp [sourceLift]

/-- Composition and the first projection form a cartesian square over the
source map. No effectiveness of the relation is assumed. -/
theorem composition_source_isPullback (e : CategoryTheory.EquivalenceRelation s t) :
    IsPullback e.t e.c.fst s s := by
  apply IsPullback.of_isLimit
    (c := PullbackCone.mk e.t e.c.fst e.transitivity₁)
  exact PullbackCone.IsLimit.mk e.transitivity₁
    (fun k => sourceLift e k.fst k.snd k.condition)
    (fun k => sourceLift_composite e k.fst k.snd k.condition)
    (fun k => sourceLift_first e k.fst k.snd k.condition)
    (fun k m hm hf => sourceLift_unique e k.fst k.snd k.condition m hm hf)

/-- Recover composable arrows from a composite and its second arrow. -/
noncomputable def targetLift (e : CategoryTheory.EquivalenceRelation s t)
    {T : C} (a b : T ⟶ R) (h : a ≫ t = b ≫ t) : T ⟶ e.c.pt :=
  PullbackCone.IsLimit.lift e.isLimit
    (compose e a (b ≫ e.s) (by simpa only [Category.assoc, e.symmetry₁] using h)) b
    (by simp [e.symmetry₂])

@[reassoc (attr := simp)]
theorem targetLift_second (e : CategoryTheory.EquivalenceRelation s t)
    {T : C} (a b : T ⟶ R) (h : a ≫ t = b ≫ t) :
    targetLift e a b h ≫ e.c.snd = b := by
  simp [targetLift]

@[reassoc (attr := simp)]
theorem targetLift_composite (e : CategoryTheory.EquivalenceRelation s t)
    {T : C} (a b : T ⟶ R) (h : a ≫ t = b ≫ t) :
    targetLift e a b h ≫ e.t = a := by
  apply e.right_cancellation
  · simp [targetLift, Category.assoc, e.transitivity₁]
  · simpa [Category.assoc, e.transitivity₂] using h.symm

/-- The second arrow and the composite determine the composable pair. -/
theorem targetLift_unique (e : CategoryTheory.EquivalenceRelation s t)
    {T : C} (a b : T ⟶ R) (h : a ≫ t = b ≫ t)
    (m : T ⟶ e.c.pt) (hm : m ≫ e.t = a) (hms : m ≫ e.c.snd = b) :
    m = targetLift e a b h := by
  apply PullbackCone.IsLimit.hom_ext e.isLimit
  · apply e.right_cancellation
    · calc
        (m ≫ e.c.fst) ≫ s = (m ≫ e.t) ≫ s := by
          simp only [Category.assoc, e.transitivity₁]
        _ = a ≫ s := by rw [hm]
        _ = (targetLift e a b h ≫ e.c.fst) ≫ s := by
          simp [targetLift]
    · calc
        (m ≫ e.c.fst) ≫ t = (m ≫ e.c.snd) ≫ s := by
          simpa only [Category.assoc] using congrArg (fun f => m ≫ f) e.c.condition
        _ = b ≫ s := by rw [hms]
        _ = (targetLift e a b h ≫ e.c.fst) ≫ t := by
          simp [targetLift, Category.assoc, e.symmetry₂]
  · simpa using hms

/-- Composition and the second projection form a cartesian square over the
target map. -/
theorem composition_target_isPullback (e : CategoryTheory.EquivalenceRelation s t) :
    IsPullback e.t e.c.snd t t := by
  apply IsPullback.of_isLimit
    (c := PullbackCone.mk e.t e.c.snd e.transitivity₂)
  exact PullbackCone.IsLimit.mk e.transitivity₂
    (fun k => targetLift e k.fst k.snd k.condition)
    (fun k => targetLift_composite e k.fst k.snd k.condition)
    (fun k => targetLift_second e k.fst k.snd k.condition)
    (fun k m hm hs => targetLift_unique e k.fst k.snd k.condition m hm hs)

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupoidIs.Construction.Groupoid
