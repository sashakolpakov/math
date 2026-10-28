import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantMonoidIsoParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.LevelPullbackGeometry

/-! # Level Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual full-level parameters for an abelian scheme over a Noetherian base. A projective presentation of the abelian family gives a quasi-projective parameter, with full levels classified on every test scheme and an actual universal full level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

abbrev Projective.LevelParameters.fullLevelLabels (g N : ℕ) := ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))

local instance Projective.LevelParameters.fullLevelLabelGroup (g N : ℕ) (S : Scheme.{u}) :
    GrpObj (ConstantScheme.Iff.constantScheme S (Projective.LevelParameters.fullLevelLabels g N)) := Geometric.GeometricLevel.constantFullLevelScheme_group g N S

theorem Projective.LevelParameters.monoidUnit_closedImmersion {S : Scheme.{u}} (X : Over S) [MonObj X] [IsSeparated X.hom] :
    IsClosedImmersion η[X].left := by
  have : IsClosedImmersion (η[X].left ≫ X.hom) := by
    rw [η[X].w]
    exact inferInstanceAs (IsClosedImmersion (𝟙 S))
  exact IsClosedImmersion.of_comp _ X.hom

variable {g : ℕ} {S : Scheme.{u}} [IsNoetherian S] (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) [NeZero N]

def Abelian.Schemes.AbelianScheme.fullLevelParameter : Over S :=
  Finite.ConstantMonoidIsoParameters.finiteConstantMonoidIsoParameter (A.torsionScheme N) (Projective.LevelParameters.fullLevelLabels g N)

def Abelian.Schemes.AbelianScheme.fullLevelParameterPointEquiv (T : Over S) :
    (T ⟶ A.fullLevelParameter N) ≃ (A.pullback T.hom).FullLevel N :=
  (Finite.ConstantMonoidIsoParameters.finiteConstantMonoidIsoParameterPointEquiv (A.torsionScheme N) (Projective.LevelParameters.fullLevelLabels g N) T).trans
    ((GroupIsomorphismData.groupIsoMorphismEquiv ((Over.pullback T.hom).obj (Level.Scheme.constantFullLevelScheme g N S))
      ((Over.pullback T.hom).obj (A.torsionScheme N))).symm.trans
        (Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv A N T.hom).symm)

def Abelian.Schemes.AbelianScheme.fullLevelParameterQuasiProjectivePresentation (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (A.fullLevelParameter N) := by
  let : IsClosedImmersion η[A.torsionScheme N].left := Projective.LevelParameters.monoidUnit_closedImmersion (A.torsionScheme N)
  exact Finite.ConstantMonoidIsoParameters.finiteConstantMonoidIsoParameterQuasiProjectivePresentation
    (A.torsionScheme N) (Projective.LevelParameters.fullLevelLabels g N) (P.ofClosedImmersion (A.torsionInclusion N)) η[A.torsionScheme N]

def Abelian.Schemes.AbelianScheme.universalFullLevel : (A.pullback (A.fullLevelParameter N).hom).FullLevel N :=
  A.fullLevelParameterPointEquiv N _ (𝟙 _)

theorem Abelian.Schemes.AbelianScheme.fullLevel_quasiProjective_point_classification (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) :
    ∃ M : Over S, Nonempty (Projective.ProjectivePresentations.QuasiProjectivePresentation M) ∧
      Nonempty ((A.pullback M.hom).FullLevel N) ∧
      ∀ T : Over S, Nonempty ((T ⟶ M) ≃ (A.pullback T.hom).FullLevel N) :=
  ⟨A.fullLevelParameter N, ⟨A.fullLevelParameterQuasiProjectivePresentation N P⟩,
    ⟨A.universalFullLevel N⟩, fun T => ⟨A.fullLevelParameterPointEquiv N T⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
