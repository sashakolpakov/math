import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceReindex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ParameterScheme
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ParameterLoci
import Mathlib.Data.Fintype.EquivFin

/-! # Projective Presentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ProjectivePresentation

noncomputable section

/-!
The constructed Grassmannian has an actual HilbertConstruction projective presentation.
The coordinate dimension is obtained from the finite Plücker index set.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem overIso_closedImmersion {S : Scheme.{u}} {X Y : Over S} (e : X ≅ Y) :
    IsClosedImmersion e.hom.left := by
  have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  infer_instance

def finiteProjectiveCoordinateEquiv (σ : Type u) [Fintype σ] [Nonempty σ] :
    σ ≃ Fin ((Fintype.card σ - 1) + 1) :=
  Fintype.equivFinOfCardEq (by
    have h := Fintype.card_pos (α := σ)
    omega)

variable {ι ν : Type u} [Fintype ι] [DecidableEq ι] [Fintype ν]
variable [Nonempty (ι → ν)]

/-- The finite Plücker embedding gives the standard projective presentation over any base. -/
def grassmannProjectivePresentation (S : Scheme.{u}) :
    Projective.ProjectivePresentations.ProjectivePresentation (ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S) where
  dimension := Fintype.card (ι → ν) - 1
  embedding := ParameterScheme.grassmannParameterEmbedding S ≫
    (Projective.SpaceReindex.relativeProjectiveSpaceReindexIso S (finiteProjectiveCoordinateEquiv (ι → ν))).hom
  closedImmersion := by
    change IsClosedImmersion ((ParameterScheme.grassmannParameterEmbedding (ι := ι) (ν := ν) S).left ≫
      (Projective.SpaceReindex.relativeProjectiveSpaceReindexIso S (finiteProjectiveCoordinateEquiv (ι → ν))).hom.left)
    exact @IsClosedImmersion.comp _ _ _ _ _
      (ParameterScheme.grassmannParameterEmbedding_isClosedImmersion S)
      (overIso_closedImmersion _)

def grassmannQuasiProjectivePresentation (S : Scheme.{u}) :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S) :=
  (grassmannProjectivePresentation S).quasiProjective

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ProjectivePresentation
