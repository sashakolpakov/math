import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.ProjectiveEmbedding
import OAI.AlgebraicGeometry.Albanese.Construction.SegreClosed

/-! # Projectivity -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Projectivity.Construction

noncomputable section

/-! Projectivity of the actual global Rees blowup of an integral projective complex scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

/-- Projective space has its identity projective presentation. -/
def identityProjectivePresentation (n : ℕ) :
    Foundations.Scheme.SmoothProjective.ProjectivePresentation (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) where
  ambientDimension := n
  embedding := 𝟙 _
  closedImmersion := inferInstance
  over_base := Category.id_comp _

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
variable [IsIntegral X] [IsLocallyNoetherian X]

/-- A closed embedding through the algebraic Segre immersion makes the
actual global blowup projective over its original complex base. -/
def globalBlowupProjectivePresentation (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f)
    (I : X.IdealSheafData) (hI : I ≠ ⊥) :
    Foundations.Scheme.SmoothProjective.ProjectivePresentation (Data.Construction.globalBlowup I hI) (Data.Construction.globalBlowupToBase I hI ≫ f) := by
  let : LocallyOfFiniteType f := P.finiteType.1
  let Q := ProjectiveMap.Construction.projectiveCenterEquations P.embedding I
  let S := Albanese.Construction.SegreClosed.tensorProjectivePresentation (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase Q.dimension))
    (Over.mk f) (identityProjectivePresentation Q.dimension) P
  let k := ProjectiveEmbedding.Construction.globalBlowupProjectiveEmbedding Q hI f
  have hk : IsClosedImmersion k := ProjectiveEmbedding.Construction.globalBlowupProjectiveEmbedding_isClosedImmersion Q hI f
  refine ⟨S.ambientDimension, k ≫ S.embedding, inferInstance, ?_⟩
  rw [Category.assoc, S.over_base]
  change k ≫ pullback.fst (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase Q.dimension) f ≫
    Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase Q.dimension = Data.Construction.globalBlowupToBase I hI ≫ f
  rw [pullback.condition, ← Category.assoc, ProjectiveEmbedding.Construction.globalBlowupProjectiveEmbedding_snd]

/-- Projectivity is obtained from the chosen presentation, without a
projectivity assumption on the blowup or any resolution-existence hypothesis. -/
theorem globalBlowup_isProjective (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f)
    (I : X.IdealSheafData) (hI : I ≠ ⊥) :
    Nonempty (Foundations.Scheme.SmoothProjective.ProjectivePresentation (Data.Construction.globalBlowup I hI) (Data.Construction.globalBlowupToBase I hI ≫ f)) :=
  ⟨globalBlowupProjectivePresentation P I hI⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Projectivity.Construction
