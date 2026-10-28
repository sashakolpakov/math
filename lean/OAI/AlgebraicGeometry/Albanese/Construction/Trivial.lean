import OAI.AlgebraicGeometry.Albanese.Construction.GeneratedClosed
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveVectorPoint

/-! # Trivial -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.Trivial

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj

/-- The complex base is projective, via the point `[1]` of projective zero-space. -/
def baseProjectivePresentation : Foundations.Scheme.SmoothProjective.ProjectivePresentation Foundations.Scheme.ProjectiveSpace.complexBase (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) := by
  let v : Fin (0 + 1) → ℂ := fun _ => 1
  have hv : v ≠ 0 := by
    intro h
    have := congrFun h 0
    exact one_ne_zero this
  let i := Foundations.Scheme.ProjectiveVectorPoint.projectiveVectorPoint v hv
  have hi : i ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 0 = 𝟙 Foundations.Scheme.ProjectiveSpace.complexBase :=
    Foundations.Scheme.ProjectiveVectorPoint.projectiveVectorPoint_over_base v hv
  exact ⟨0, i, isClosedImmersion_of_comp_eq_id (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 0) i hi, hi⟩

/-- A concrete smooth projective presentation of the one-point complex scheme. -/
def baseSmoothProjectivePresentation : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation where
  carrier := Foundations.Scheme.ProjectiveSpace.complexBase
  structureMap := 𝟙 Foundations.Scheme.ProjectiveSpace.complexBase
  projective := baseProjectivePresentation
  smooth := inferInstance

/-- The zero-dimensional abelian variety with its actual projective embedding. -/
def trivialAbelianVariety : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety where
  variety := ⟨baseSmoothProjectivePresentation, inferInstanceAs (IsIntegral Foundations.Scheme.ProjectiveSpace.complexBase)⟩
  group := inferInstanceAs (GrpObj (𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase)))
  commutative := inferInstanceAs (IsCommMonObj (𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase)))

/-- There is always at least one pointed generating target. -/
theorem exists_pointed_generating_target (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) :
    ∃ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver),
      x₀ ≫ a = 1 ∧ GeneratedClosed.Generates X A a := by
  refine ⟨trivialAbelianVariety, 1, by simp, ?_⟩
  apply top_unique
  intro p _
  have hp : p = 1 := by
    exact Subsingleton.elim (α := Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ 𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase)) p 1
  rw [hp]
  exact Subgroup.one_mem _

end

end OAI.AlgebraicGeometry.Albanese.Construction.Trivial
