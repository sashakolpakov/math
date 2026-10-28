import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.Subsite
import Mathlib.CategoryTheory.Sites.Over

/-! # Subsite Slices -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SubsiteSlices

noncomputable section

/-!
# IntegralComparison: slices of an incoming-closed full subsite are the original slices

Every object over a subsite object already satisfies its defining
property. The native slice inclusion is therefore an equivalence, and
the native restricted slice topology agrees with the original one.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)
  (hP : ∀ {X Y : C}, (X ⟶ Y) → P Y → P X) (U : P.FullSubcategory)

def liftObject (V : Over U.obj) : Over U :=
  Over.mk (ObjectProperty.homMk (X := ⟨V.left, hP V.hom U.property⟩) (Y := U) V.hom)

theorem post_liftObject (V : Over U.obj) : (Over.post P.ι).obj (liftObject P hP U V) = V := by
  cases V
  rfl

include hP in
theorem post_isEquivalence : (Over.post (X := U) P.ι).IsEquivalence := by
  let : (Over.post (X := U) P.ι).EssSurj :=
    ⟨fun V => ⟨liftObject P hP U V, ⟨eqToIso (post_liftObject P hP U V)⟩⟩⟩
  exact {}

def equivalence : Over U ≌ Over U.obj := by
  have := post_isEquivalence P hP U
  exact (Over.post (X := U) P.ι).asEquivalence

variable (J : GrothendieckTopology C)

include hP in
theorem post_isDenseSubsite : (Over.post (X := U) P.ι).IsDenseSubsite
    ((P.ι.restrictedTopology J).over U) (J.over U.obj) := by
  have := Subsite.continuous P hP J
  have := Subsite.cocontinuous P hP J
  have := post_isEquivalence P hP U
  let F := Over.post (X := U) P.ι
  have hcover : CoverPreserving ((P.ι.restrictedTopology J).over U) (J.over U.obj) F :=
    (CoverPreserving.of_isContinuous P.ι (P.ι.restrictedTopology J) J).overPost U
  have : F.IsContinuous ((P.ι.restrictedTopology J).over U) (J.over U.obj) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ F) hcover
  have : F.IsCocontinuous ((P.ι.restrictedTopology J).over U) (J.over U.obj) := by
    constructor
    intro V S hS
    rw [GrothendieckTopology.mem_over_iff] at hS ⊢
    rw [Sieve.overEquiv_functorPullback_post]
    exact P.ι.cover_lift (P.ι.restrictedTopology J) J hS
  refine { functorPushforward_mem_iff := ?_ }
  intro V S
  constructor
  · intro hS
    have h := F.cover_lift ((P.ι.restrictedTopology J).over U) (J.over U.obj) hS
    change (S.functorPushforward F).functorPullback F ∈ ((P.ι.restrictedTopology J).over U) V at h
    simpa only [Sieve.functorPullback_functorPushforward_eq] using h
  · exact hcover.cover_preserve

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SubsiteSlices
