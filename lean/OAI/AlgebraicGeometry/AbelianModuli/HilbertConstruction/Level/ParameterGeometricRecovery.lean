import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.LevelParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantMonoidIsoRepresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.GeometricPointDiagram

/-! # Parameter Geometric Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The full-level parameter equivalence recovers exactly the represented
torsion isomorphism. In particular its action on every ordered test-scheme
basis is determined by the native geometric point of the parameter. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.Obj
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance Level.ParameterGeometricRecovery.levelRecoveryConstantGroup (g N : ℕ) (S : Scheme.{u}) :
    GrpObj (ConstantScheme.Iff.constantScheme S (Projective.LevelParameters.fullLevelLabels g N)) := Geometric.GeometricLevel.constantFullLevelScheme_group g N S

variable {g : ℕ} {S : Scheme.{u}} [IsNoetherian S] (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) [NeZero N]
variable (T : Over S) (y : T ⟶ A.fullLevelParameter N)

theorem Abelian.Schemes.AbelianScheme.fullLevelParameterPointEquiv_geometric :
    GroupIsomorphismData.groupIsoMorphismEquiv
      ((Over.pullback T.hom).obj (Level.Scheme.constantFullLevelScheme g N S))
      ((Over.pullback T.hom).obj (A.torsionScheme N))
      (Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv A N T.hom (A.fullLevelParameterPointEquiv N T y)) =
        Finite.ConstantMonoidIsoParameters.finiteConstantMonoidIsoParameterPointEquiv (A.torsionScheme N) (Projective.LevelParameters.fullLevelLabels g N) T y := by
  change GroupIsomorphismData.groupIsoMorphismEquiv _ _
    (Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv A N T.hom
      ((Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv A N T.hom).symm
        ((GroupIsomorphismData.groupIsoMorphismEquiv _ _).symm
          (Finite.ConstantMonoidIsoParameters.finiteConstantMonoidIsoParameterPointEquiv (A.torsionScheme N)
            (Projective.LevelParameters.fullLevelLabels g N) T y)))) = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem Abelian.Schemes.AbelianScheme.fullLevelParameterPointEquiv_geometric_hom :
    (Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv A N T.hom
      (A.fullLevelParameterPointEquiv N T y)).hom.hom.hom =
        (Finite.ConstantMonoidIsoParameters.finiteConstantMonoidIsoParameterPointEquiv (A.torsionScheme N)
          (Projective.LevelParameters.fullLevelLabels g N) T y).val.val :=
  congrArg (fun z => z.val.val) (A.fullLevelParameterPointEquiv_geometric N T y)

theorem Abelian.Schemes.AbelianScheme.fullLevelParameterPointEquiv_point (U : Over T.left)
    (q : U ⟶ (Over.pullback T.hom).obj (Level.Scheme.constantFullLevelScheme g N S)) :
    (A.torsionPullbackYonedaIso N T.hom).hom.app (.op U)
      (q ≫ (Finite.ConstantMonoidIsoParameters.finiteConstantMonoidIsoParameterPointEquiv (A.torsionScheme N)
        (Projective.LevelParameters.fullLevelLabels g N) T y).val.val) =
      (A.fullLevelParameterPointEquiv N T y).hom.app (.op U)
        ((Level.LevelPullbackGeometry.constantFullLevelBaseChangeYonedaIso g N T.hom).hom.app (.op U) q) := by
  rw [← A.fullLevelParameterPointEquiv_geometric_hom N T y]
  exact Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv_point A N T.hom
    (A.fullLevelParameterPointEquiv N T y) U q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
