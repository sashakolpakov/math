import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.EvaluationBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterUnitValues

/-! # Multiplicative Unit Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.MultiplicativeUnitBaseChange.Construction

noncomputable section

/-! The native multiplicative-group base-change comparison preserves the
actual unit of functions represented by each test-scheme point. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.EvaluationBaseChange.Construction OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes

theorem multiplicativeGroup_pullbackIso_hom_integralProjection
    {S T : Scheme.{u}} (s : T ⟶ S) :
    (CartierDuality.SliceCharacters.Construction.Schemes.multiplicativeGroup_pullbackIso s).hom.hom.hom.left ≫ CartierDuality.SliceCharacters.Construction.Schemes.multiplicativeGroupToIntegral T =
      pullback.fst (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X.hom s ≫ CartierDuality.SliceCharacters.Construction.Schemes.multiplicativeGroupToIntegral S := by
  let e := ((Grp.forget (Over T)) ⋙ Over.forget T).mapIso (CartierDuality.SliceCharacters.Construction.Schemes.multiplicativeGroup_pullbackIso s)
  exact (congrArg (fun t => e.hom ≫ t)
    (CartierDuality.SliceCharacters.Construction.Schemes.multiplicativeGroup_pullbackIso_inv_integralProjection s).symm).trans
      (e.hom_inv_id_assoc _)

theorem multiplicativeGroupPointBaseChange_integralProjection
    {S T : Scheme.{u}} (s : T ⟶ S) (U : Over T)
    (x : (Over.map s).obj U ⟶ (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) :
    (CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange s U x).left ≫ CartierDuality.SliceCharacters.Construction.Schemes.multiplicativeGroupToIntegral T =
      x.left ≫ CartierDuality.SliceCharacters.Construction.Schemes.multiplicativeGroupToIntegral S := by
  let G := CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S
  let y := CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s G U x
  have hx := congrArg (fun z : (Over.map s).obj U ⟶ G.X => z.left)
    (((Over.mapPullbackAdj s).homEquiv U G.X).symm_apply_apply x)
  change y.left ≫ pullback.fst G.X.hom s = x.left at hx
  change (y.left ≫ (CartierDuality.SliceCharacters.Construction.Schemes.multiplicativeGroup_pullbackIso s).hom.hom.hom.left) ≫
    CartierDuality.SliceCharacters.Construction.Schemes.multiplicativeGroupToIntegral T = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => y.left ≫ t)
      (multiplicativeGroup_pullbackIso_hom_integralProjection s)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun t => t ≫ CartierDuality.SliceCharacters.Construction.Schemes.multiplicativeGroupToIntegral S) hx)))

theorem multiplicativeGroupUnitHom_value {S : Scheme.{u}} (T : Over S)
    (x : T ⟶ (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) :
    (CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T x).val =
      (x.left ≫ CartierDuality.SliceCharacters.Construction.Schemes.multiplicativeGroupToIntegral S).appTop
        (CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection (CartierDuality.Characters.Construction.MultiplicativeGroupCoordinate (ULift.{u} ℤ))
          CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupGenerator.val) := rfl

theorem multiplicativeGroupUnitHom_baseChange {S T : Scheme.{u}} (s : T ⟶ S) (U : Over T)
    (x : (Over.map s).obj U ⟶ (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) :
    CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom U (CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange s U x) =
      CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom ((Over.map s).obj U) x := by
  apply Units.ext
  exact (multiplicativeGroupUnitHom_value U _).trans
    ((congrArg (fun t => t.appTop
      (CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection (CartierDuality.Characters.Construction.MultiplicativeGroupCoordinate (ULift.{u} ℤ))
        CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupGenerator.val))
      (multiplicativeGroupPointBaseChange_integralProjection s U x)).trans
        (multiplicativeGroupUnitHom_value ((Over.map s).obj U) x).symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.MultiplicativeUnitBaseChange.Construction
