import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.BaseChangeReferencePoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackMonoidIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Transport

/-! # Parameter Level Point Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The canonical parameter pullback map preserves the original points
and their ordered constant labels. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {U T : Over S} (c : U ⟶ T) (X : Over S)

def ParameterLevelPointComparison.parameterPointToLargerBase (V : Over U.left) (q : V ⟶ (Over.pullback U.hom).obj X) :
    (Over.map c.left).obj V ⟶ (Over.pullback T.hom).obj X :=
  Over.homMk (q.left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap c X) (by
    rw [Category.assoc, Single.ParameterFunctoriality.singleParameterBaseChangeMap_over, ← Category.assoc, q.w]
    rfl)

theorem ParameterLevelPointComparison.parameterPointToLargerBase_fst (V : Over U.left)
    (q : V ⟶ (Over.pullback U.hom).obj X) :
    (ParameterLevelPointComparison.parameterPointToLargerBase c X V q).left ≫ pullback.fst X.hom T.hom =
      q.left ≫ pullback.fst X.hom U.hom := by
  change (q.left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap c X) ≫ pullback.fst X.hom T.hom = _
  rw [Category.assoc, Single.ParameterBaseChange.singleParameterBaseChangeMap_comp]

theorem ParameterLevelPointComparison.singleParameterBaseChangeIso_inv_original_fst :
    (Single.ParameterBaseChange.singleParameterBaseChangeIso c X).inv.left ≫ pullback.fst X.hom U.hom =
      pullback.fst ((Over.pullback T.hom).obj X).hom c.left ≫ pullback.fst X.hom T.hom := by
  rw [← Single.ParameterBaseChange.singleParameterBaseChangeMap_comp c X, ← Category.assoc,
    Single.ParameterFunctoriality.singleParameterBaseChangeIso_inv_comp]

theorem ParameterLevelPointComparison.constantLevelLabels_parameterPoint (g N : ℕ) (V : Over U.left)
    (q : V ⟶ (Over.pullback U.hom).obj (Level.Scheme.constantFullLevelScheme g N S)) :
    (Level.LevelPullbackGeometry.constantFullLevelBaseChangeYonedaIso g N T.hom).hom.app (.op ((Over.map c.left).obj V))
      (ParameterLevelPointComparison.parameterPointToLargerBase c (Level.Scheme.constantFullLevelScheme g N S) V q) =
        (Level.LevelPullbackGeometry.constantFullLevelBaseChangeYonedaIso g N U.hom).hom.app (.op V) q := by
  have h := ParameterLevelPointComparison.parameterPointToLargerBase_fst c (Level.Scheme.constantFullLevelScheme g N S) V q
  apply LocallyConstant.ext
  intro v
  change (ConstantScheme.Iff.constantSchemeIndex S (ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)))
    (((ParameterLevelPointComparison.parameterPointToLargerBase c (Level.Scheme.constantFullLevelScheme g N S) V q).left ≫
      pullback.fst (Level.Scheme.constantFullLevelScheme g N S).hom T.hom) v)).down =
    (ConstantScheme.Iff.constantSchemeIndex S (ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)))
      ((q.left ≫ pullback.fst (Level.Scheme.constantFullLevelScheme g N S).hom U.hom) v)).down
  rw [h]

variable {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

def Abelian.Schemes.AbelianScheme.parameterPullbackIso :
    (A.pullback U.hom).scheme ≅ ((A.pullback T.hom).pullback c.left).scheme :=
  Single.ParameterBaseChange.singleParameterBaseChangeIso c A.scheme

instance Abelian.Schemes.AbelianScheme.parameterPullbackIso_isMonHom : IsMonHom (A.parameterPullbackIso c).hom :=
  ParameterPullbackMonoidIso.singleParameterBaseChangeIso_isMonHom c A.scheme

instance Abelian.Schemes.AbelianScheme.parameterPullbackIso_symm_isMonHom : IsMonHom (A.parameterPullbackIso c).symm.hom :=
  inferInstanceAs (IsMonHom (A.parameterPullbackIso c).inv)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
