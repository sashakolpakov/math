import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupIsomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Scheme
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantScheme

/-! # Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Explicit parameters for changing a chosen full level structure. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {g N : ℕ} {S : Scheme.{u}}

/-- Automorphisms of the finite standard ordered-level group. -/
abbrev Level.Parameters.LevelLabelAut (g N : ℕ) :=
  Multiplicative (Fin (2 * g) → ZMod N) ≃* Multiplicative (Fin (2 * g) → ZMod N)

section

variable {A : Abelian.Schemes.AbelianScheme g S}

/-- Relative to a chosen level, every level is a change of the standard ordered labels. -/
def Abelian.Schemes.AbelianScheme.FullLevel.changeEquiv (base : A.FullLevel N) : A.FullLevel N ≃
    (Constant.GroupMaps.constantGroupFunctor S (Multiplicative (Fin (2 * g) → ZMod N)) ≅
      Constant.GroupMaps.constantGroupFunctor S (Multiplicative (Fin (2 * g) → ZMod N))) where
  toFun level := level ≪≫ base.symm
  invFun e := e ≪≫ base
  left_inv level := by
    apply Iso.ext
    change (level.hom ≫ base.inv) ≫ base.hom = level.hom
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun a => level.hom ≫ a) base.inv_hom_id).trans (Category.comp_id _))
  right_inv e := by
    apply Iso.ext
    change (e.hom ≫ base.hom) ≫ base.inv = e.hom
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun a => e.hom ≫ a) base.hom_inv_id).trans (Category.comp_id _))

/-- Changes of level over an arbitrary base are locally constant label automorphisms. -/
def Abelian.Schemes.AbelianScheme.FullLevel.labelsEquiv [NeZero N] (base : A.FullLevel N) :
    A.FullLevel N ≃ LocallyConstant S (Level.Parameters.LevelLabelAut g N) :=
  base.changeEquiv.trans Constant.GroupIsomorphisms.constantGroupIsoEquiv

end

/-- The split scheme of changes of ordered full level. -/
def Level.Parameters.levelParameterScheme (g N : ℕ) (S : Scheme.{u}) : Over S :=
  ConstantScheme.Iff.constantScheme S (ULift.{u} (Level.Parameters.LevelLabelAut g N))

/-- After fixing a level, morphisms into its parameter scheme classify all levels on
every base-changed abelian scheme. -/
def Abelian.Schemes.AbelianScheme.FullLevel.parameterEquiv {A : Abelian.Schemes.AbelianScheme g S} [NeZero N]
    (base : A.FullLevel N) (T : Over S) :
    (T ⟶ Level.Parameters.levelParameterScheme g N S) ≃ (A.pullback T.hom).FullLevel N :=
  ((ConstantScheme.Iff.constantSchemePointsEquiv S _ T).trans (LocallyConstant.congrRight Equiv.ulift)).trans
    ((base.pullback T.hom).labelsEquiv).symm

instance Level.Parameters.levelParameterScheme_etale (g N : ℕ) (S : Scheme.{u}) :
    Etale (Level.Parameters.levelParameterScheme g N S).hom := Level.Scheme.constantScheme_etale S _

instance Level.Parameters.levelParameterScheme_finite (g N : ℕ) (S : Scheme.{u}) [NeZero N] :
    IsFinite (Level.Parameters.levelParameterScheme g N S).hom := Finite.ConstantScheme.constantScheme_finite

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
