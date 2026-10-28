import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ConditionRepresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ImmersionFactorization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ParameterLoci

/-! # Condition Intersections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ConditionIntersections

noncomputable section

/-!
Simultaneous closed conditions are represented by the sum of their defining
ideals. This constructs intersections of parameter loci with their full
scheme structure and unique factorization property.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {S : Scheme.{u}} {M : Over S} {α : Type v}
variable (P : α → Subfunctor (yoneda.obj M)) (D : ∀ i, ConditionIdeals.ClosedConditionModel (P i))

def closedConditionIntersection : Subfunctor (yoneda.obj M) where
  obj T := {f | ∀ i, f ∈ (P i).obj T}
  map g _f hf i := (P i).map g (hf i)

def closedConditionIntersectionIdeal : M.left.IdealSheafData := ⨆ i, (D i).ideal

theorem closedConditionIntersectionIdeal_vanish_iff {T : Over S} (f : T ⟶ M) :
    (closedConditionIntersectionIdeal P D).comap f.left = ⊥ ↔
      f ∈ (closedConditionIntersection P).obj (.op T) := by
  rw [ConditionIdeals.ideal_comap_eq_bot_iff]
  change (⨆ i, (D i).ideal) ≤ f.left.ker ↔ ∀ i, f ∈ (P i).obj (.op T)
  rw [iSup_le_iff]
  exact forall_congr' (fun i => (ConditionIdeals.ideal_comap_eq_bot_iff (D i).ideal f.left).symm.trans
    ((D i).ideal_vanish_iff f))

def closedConditionIntersectionScheme : Over S :=
  Over.mk ((closedConditionIntersectionIdeal P D).subschemeι ≫ M.hom)

def closedConditionIntersectionInclusion : closedConditionIntersectionScheme P D ⟶ M :=
  Over.homMk (closedConditionIntersectionIdeal P D).subschemeι rfl

instance closedConditionIntersectionInclusion_closed :
    IsClosedImmersion (closedConditionIntersectionInclusion P D).left :=
  inferInstanceAs (IsClosedImmersion (closedConditionIntersectionIdeal P D).subschemeι)

def closedConditionIntersectionModel : ConditionIdeals.ClosedConditionModel (closedConditionIntersection P) where
  scheme := closedConditionIntersectionScheme P D
  inclusion := closedConditionIntersectionInclusion P D
  closed := closedConditionIntersectionInclusion_closed P D
  factorization T f := by
    have h := ImmersionFactorization.closedImmersion_ideal_factorization (closedConditionIntersectionInclusion P D) f
    change (closedConditionIntersectionIdeal P D).subschemeι.ker.comap f.left = ⊥ ↔ _ at h
    rw [(closedConditionIntersectionIdeal P D).ker_subschemeι] at h
    exact (closedConditionIntersectionIdeal_vanish_iff P D f).symm.trans h

def closedConditionIntersectionRepresentation :
    yoneda.obj (closedConditionIntersectionScheme P D) ≅ (closedConditionIntersection P).toFunctor :=
  (closedConditionIntersectionModel P D).representation

def closedConditionIntersectionProjective (Q : Projective.ProjectivePresentations.ProjectivePresentation M) :
    Projective.ProjectivePresentations.ProjectivePresentation (closedConditionIntersectionScheme P D) :=
  Q.ofClosedImmersion (closedConditionIntersectionInclusion P D)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ConditionIntersections
