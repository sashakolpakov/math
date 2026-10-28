import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.IncidenceGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ParameterLoci

/-! # Incidence Scheme -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.IncidenceScheme

noncomputable section

/-!
The global closed incidence scheme for two Grassmannian maps and a fixed linear
map of ambient coordinate modules. Its full defining ideal is constructed by
gluing the checked normalized-chart equations.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ : Type u}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ]
variable {S : Scheme.{u}} {M : Over S}
variable (q : M ⟶ ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S)
variable (k : M ⟶ ParameterScheme.grassmannParameterScheme (ι := κ) (ν := μ) S)
variable (F : Matrix μ ν Γ(M.left, ⊤))

def grassmannIncidenceIdeal : M.left.IdealSheafData :=
  (PairChartCover.grassmannPairChartCover q k).incidenceIdeal F

def grassmannIncidenceScheme : Over S :=
  Over.mk ((grassmannIncidenceIdeal q k F).subschemeι ≫ M.hom)

def grassmannIncidenceInclusion : grassmannIncidenceScheme q k F ⟶ M :=
  Over.homMk (grassmannIncidenceIdeal q k F).subschemeι rfl

instance grassmannIncidenceInclusion_isClosedImmersion :
    IsClosedImmersion (grassmannIncidenceInclusion q k F).left :=
  inferInstanceAs (IsClosedImmersion (grassmannIncidenceIdeal q k F).subschemeι)

theorem grassmannIncidenceInclusion_kernel :
    (grassmannIncidenceInclusion q k F).left.ker = grassmannIncidenceIdeal q k F :=
  (grassmannIncidenceIdeal q k F).ker_subschemeι

theorem grassmannIncidenceIdeal_on_chart (i : (PairChartCover.grassmannPairChartCover q k).cover.I₀) :
    (grassmannIncidenceIdeal q k F).comap ((PairChartCover.grassmannPairChartCover q k).cover.f i) =
      (PairChartCover.grassmannPairChartCover q k).incidenceLocalIdeal F i :=
  (PairChartCover.grassmannPairChartCover q k).incidenceIdeal_comap F i

/-- Closed incidence inside a projective parameter scheme is projective over the same base. -/
def grassmannIncidenceProjectivePresentation (P : Projective.ProjectivePresentations.ProjectivePresentation M) :
    Projective.ProjectivePresentations.ProjectivePresentation (grassmannIncidenceScheme q k F) :=
  P.ofClosedImmersion (grassmannIncidenceInclusion q k F)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.IncidenceScheme
