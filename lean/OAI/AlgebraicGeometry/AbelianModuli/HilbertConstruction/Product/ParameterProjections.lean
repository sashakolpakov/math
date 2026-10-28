import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.ParameterBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.ParameterBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.BaseChangeNaturality

/-! # Parameter Projections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.ParameterProjections

noncomputable section

/-! Geometric comparison of parameter products preserves both source and target projections exactly. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

theorem overProductBaseChangeMap_fst {S T : Scheme.{u}} (f : T ⟶ S) (A B : Over S) :
    Graph.FamilyNaturality.overProductBaseChangeMap f A B ≫ (fst A B).left =
      (fst ((Over.pullback f).obj A) ((Over.pullback f).obj B)).left ≫ pullback.fst A.hom f := by
  change ((Functor.Monoidal.μIso (Over.pullback f) A B).hom.left ≫ pullback.fst (A ⊗ B).hom f) ≫
    pullback.fst A.hom B.hom = _
  rw [Category.assoc]
  exact Over.μ_pullback_left_fst_fst A B

theorem overProductBaseChangeMap_snd {S T : Scheme.{u}} (f : T ⟶ S) (A B : Over S) :
    Graph.FamilyNaturality.overProductBaseChangeMap f A B ≫ (snd A B).left =
      (snd ((Over.pullback f).obj A) ((Over.pullback f).obj B)).left ≫ pullback.fst B.hom f := by
  change ((Functor.Monoidal.μIso (Over.pullback f) A B).hom.left ≫ pullback.fst (A ⊗ B).hom f) ≫
    pullback.snd A.hom B.hom = _
  rw [Category.assoc]
  exact Over.μ_pullback_left_fst_snd A B

theorem productParameterBaseChangeMap_fst {S : Scheme.{u}} {T M : Over S} (f : T ⟶ M) (A B : Over S) :
    ParameterBaseChange.productParameterBaseChangeMap f A B ≫ (fst ((Over.pullback M.hom).obj A) ((Over.pullback M.hom).obj B)).left =
      (fst ((Over.pullback T.hom).obj A) ((Over.pullback T.hom).obj B)).left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap f A :=
  Cartesian.BaseChangeNaturality.cartesianBaseChangeMap_natural (A := A ⊗ B) (B := A)
    (X₁ := ParameterBaseChange.parameterProductFamily A B T) (Y₁ := ParameterBaseChange.parameterProductFamily A B M)
    (X₂ := (Over.pullback T.hom).obj A) (Y₂ := (Over.pullback M.hom).obj A) f.left M.hom
    (Graph.FamilyNaturality.overProductBaseChangeMap T.hom A B) (Graph.FamilyNaturality.overProductBaseChangeMap M.hom A B)
    (pullback.fst A.hom T.hom) (pullback.fst A.hom M.hom)
    (ParameterBaseChange.parameterProductFamily_composite_isPullback f A B) (Graph.FamilyNaturality.overProductBaseChange_isPullback M.hom A B)
    (Single.ParameterBaseChange.parameterFamily_composite_isPullback f A) (IsPullback.of_hasPullback A.hom M.hom)
    (fst ((Over.pullback T.hom).obj A) ((Over.pullback T.hom).obj B))
    (fst ((Over.pullback M.hom).obj A) ((Over.pullback M.hom).obj B))
    (fst A B) (overProductBaseChangeMap_fst T.hom A B) (overProductBaseChangeMap_fst M.hom A B)

theorem productParameterBaseChangeMap_snd {S : Scheme.{u}} {T M : Over S} (f : T ⟶ M) (A B : Over S) :
    ParameterBaseChange.productParameterBaseChangeMap f A B ≫ (snd ((Over.pullback M.hom).obj A) ((Over.pullback M.hom).obj B)).left =
      (snd ((Over.pullback T.hom).obj A) ((Over.pullback T.hom).obj B)).left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap f B :=
  Cartesian.BaseChangeNaturality.cartesianBaseChangeMap_natural (A := A ⊗ B) (B := B)
    (X₁ := ParameterBaseChange.parameterProductFamily A B T) (Y₁ := ParameterBaseChange.parameterProductFamily A B M)
    (X₂ := (Over.pullback T.hom).obj B) (Y₂ := (Over.pullback M.hom).obj B) f.left M.hom
    (Graph.FamilyNaturality.overProductBaseChangeMap T.hom A B) (Graph.FamilyNaturality.overProductBaseChangeMap M.hom A B)
    (pullback.fst B.hom T.hom) (pullback.fst B.hom M.hom)
    (ParameterBaseChange.parameterProductFamily_composite_isPullback f A B) (Graph.FamilyNaturality.overProductBaseChange_isPullback M.hom A B)
    (Single.ParameterBaseChange.parameterFamily_composite_isPullback f B) (IsPullback.of_hasPullback B.hom M.hom)
    (snd ((Over.pullback T.hom).obj A) ((Over.pullback T.hom).obj B))
    (snd ((Over.pullback M.hom).obj A) ((Over.pullback M.hom).obj B))
    (snd A B) (overProductBaseChangeMap_snd T.hom A B) (overProductBaseChangeMap_snd M.hom A B)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.ParameterProjections
