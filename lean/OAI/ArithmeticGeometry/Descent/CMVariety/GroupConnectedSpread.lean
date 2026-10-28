import OAI.ArithmeticGeometry.Descent.CMVariety.OpenGroupGeneration
import OAI.ArithmeticGeometry.Descent.CMVariety.OpenSurjectivitySpread
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeneratingFiberConnectedness

/-! # Group Connected Spread -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.GroupConnectedSpread.Abelian

noncomputable section

/-! A smooth proper group coefficient model with connected complex fiber
becomes geometrically connected once it contains a geometrically connected
open. The good open and the later coefficient enlargement are constructive. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeneratingFiberConnectedness

theorem group_model_with_good_open_eventually_connected
    {R K : Type} [CommRing R] [Field K] [IsAlgClosed K] [Algebra R K] {s : Finset K}
    (M : Over (Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s)) [GrpObj M] [Smooth M.hom] [IsProper M.hom]
    [IrreducibleSpace ((Over.pullback (Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)).obj M).left]
    (V : Over (Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s)) [GeometricallyConnected V.hom]
    (i : V ⟶ M) [IsOpenImmersion i.left] :
    ∃ (t : Finset K) (h : s ⊆ t),
      GeometricallyConnected ((Over.pullback (Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)).obj M).hom := by
  have : Smooth V.hom := by
    rw [← i.w]
    infer_instance
  have : GeometricallyConnected (V ⊗ V).hom := AlgebraicGeometry.PELModuli.IntegralModel.GeneratingFiberConnectedness.geometricallyConnected_tensor V V
  let F := Over.pullback (Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)
  let j := F.map i
  have : Smooth (F.obj M).hom := inferInstanceAs (Smooth (pullback.snd M.hom (Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)))
  have : GeometricallyConnected (F.obj V).hom := inferInstanceAs
    (GeometricallyConnected (pullback.snd V.hom (Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)))
  have : Nonempty (F.obj V).left := by
    have : ConnectedSpace (F.obj V).left :=
      GeometricallyConnected.connectedSpace_of_subsingleton (F.obj V).hom
    infer_instance
  have : IsOpenImmersion j.left := MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
    (Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s) i inferInstance
  have hj : Surjective (EmbeddedGroupCoefficients.Abelian.groupOpenProduct j).left := OpenGroupGeneration.Abelian.open_group_product_surjective j
  let e := prodComparisonIso F V V
  have : IsIso e.hom.left := ((Over.forget (Spec (.of K))).mapIso e).isIso_hom
  have hgeneric : Surjective (F.map (EmbeddedGroupCoefficients.Abelian.groupOpenProduct i)).left := by
    rw [EmbeddedGroupCoefficients.Abelian.groupOpenProduct_pullback]
    exact inferInstanceAs (Surjective (e.hom.left ≫ (EmbeddedGroupCoefficients.Abelian.groupOpenProduct j).left))
  have : Smooth (EmbeddedGroupCoefficients.Abelian.groupOpenProduct i).left := EmbeddedGroupCoefficients.Abelian.groupOpenProduct_smooth i
  obtain ⟨t, h, hs⟩ := OpenSurjectivitySpread.Abelian.open_map_to_proper_family_eventually_surjective
    (EmbeddedGroupCoefficients.Abelian.groupOpenProduct i) (EmbeddedGroupCoefficients.Abelian.groupOpenProduct i).left.isOpenMap hgeneric
  let B := Over.pullback (Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)
  have : Surjective (B.map (EmbeddedGroupCoefficients.Abelian.groupOpenProduct i)).left := hs
  have : GeometricallyConnected (B.obj (V ⊗ V)).hom := inferInstanceAs
    (GeometricallyConnected (pullback.snd (V ⊗ V).hom (Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)))
  exact ⟨t, h, AlgebraicGeometry.PELModuli.IntegralModel.GeneratingFiberConnectedness.geometricallyConnected_of_surjective_map (B.map (EmbeddedGroupCoefficients.Abelian.groupOpenProduct i))⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.GroupConnectedSpread.Abelian
