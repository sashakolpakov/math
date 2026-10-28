import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Monomorphism Local Lifts -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.MonomorphismLocalLifts.Construction

noncomputable section

/-! Lifts to a monomorphism glue uniquely from an open cover. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

theorem mono_hasLift_of_openCover {S : Scheme.{u}} (M T : Over S) [Mono M.hom]
    (U : T.left.OpenCover)
    (h : ∀ i, Nonempty (Over.mk (U.f i ≫ T.hom) ⟶ M)) : Nonempty (T ⟶ M) := by
  let v := fun i => Classical.choice (h i)
  have hv : ∀ i j, pullback.fst (U.f i) (U.f j) ≫ (v i).left =
      pullback.snd (U.f i) (U.f j) ≫ (v j).left := by
    intro i j
    apply (cancel_mono M.hom).mp
    simp only [Category.assoc, (v i).w, (v j).w]
    exact pullback.condition_assoc T.hom
  let w := U.glueMorphisms (fun i => (v i).left) hv
  refine ⟨Over.homMk w ?_⟩
  apply U.hom_ext
  intro i
  rw [← Category.assoc, U.ι_glueMorphisms]
  exact (v i).w

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.MonomorphismLocalLifts.Construction
