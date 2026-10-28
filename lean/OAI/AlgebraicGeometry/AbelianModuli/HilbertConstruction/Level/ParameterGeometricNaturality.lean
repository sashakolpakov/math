import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.ParameterGeometricRecovery

/-! # Parameter Geometric Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The geometric torsion isomorphism classified by the full-level
parameter commutes with arbitrary changes of the parameter scheme. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance Level.ParameterGeometricNaturality.levelNaturalityConstantGroup (g N : ℕ) (S : Scheme.{u}) :
    GrpObj (ConstantScheme.Iff.constantScheme S (Projective.LevelParameters.fullLevelLabels g N)) := Geometric.GeometricLevel.constantFullLevelScheme_group g N S

variable {g : ℕ} {S : Scheme.{u}} [IsNoetherian S] (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) [NeZero N]

theorem Abelian.Schemes.AbelianScheme.fullLevelParameterPointEquiv_geometric_natural {U T : Over S} (c : U ⟶ T)
    (y : T ⟶ A.fullLevelParameter N) :
    (Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv A N U.hom
      (A.fullLevelParameterPointEquiv N U (c ≫ y))).hom.hom.hom =
        Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c
          (Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv A N T.hom
            (A.fullLevelParameterPointEquiv N T y)).hom.hom.hom := by
  rw [A.fullLevelParameterPointEquiv_geometric_hom N U (c ≫ y),
    A.fullLevelParameterPointEquiv_geometric_hom N T y]
  have h := ConcreteCategory.congr_hom (CC := fun X : Type u => X)
    ((Finite.ConstantMonoidIsoRepresentation.finiteConstantMonoidIsoClassifyingIso (A.torsionScheme N) (Projective.LevelParameters.fullLevelLabels g N)).hom.naturality c.op) y
  exact congrArg (fun z => z.val.val) h

theorem Abelian.Schemes.AbelianScheme.universalFullLevel_geometric_point {T : Over S} (y : T ⟶ A.fullLevelParameter N) :
    (Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv A N T.hom
      (A.fullLevelParameterPointEquiv N T y)).hom.hom.hom =
        Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange y
          (Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv A N (A.fullLevelParameter N).hom
            (A.universalFullLevel N)).hom.hom.hom := by
  have h := A.fullLevelParameterPointEquiv_geometric_natural N y (𝟙 (A.fullLevelParameter N))
  simp only [Category.comp_id] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
