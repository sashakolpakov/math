import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SplitLocalizedModels
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComplexComparison
import OAI.AlgebraicGeometry.PELModuli.CMPoints.AbelianModelDimension
import OAI.AlgebraicGeometry.PELModuli.CMPoints.GroupMapReflection

/-! # Abelian Diagram Spreading -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.AbelianDiagramSpreading

noncomputable section

/-! The proved SpreadingOut/IntegralModel model theorem spreads a finite diagram of
actual arithmetic abelian schemes, retaining relative dimensions and
the group laws of every arrow. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

structure FiniteAbelianDiagram (K : Type) [Field K] [NumberField K] where
  objects : ℕ
  arrows : ℕ
  dimension : Fin objects → ℕ
  abelian : ∀ i, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (dimension i) (Spec (.of K))
  source : Fin arrows → Fin objects
  target : Fin arrows → Fin objects
  map : ∀ a, (abelian (source a)).scheme ⟶ (abelian (target a)).scheme
  group : ∀ a, IsMonHom (map a)

def FiniteAbelianDiagram.toFiniteDiagram
    {K : Type} [Field K] [NumberField K] (D : FiniteAbelianDiagram K) : IntegralModel.ModelsHas.FiniteDiagram K where
  objects := Fin D.objects
  arrows := Fin D.arrows
  abelians := Fin D.objects
  X i := (D.abelian i).scheme
  smooth _ := inferInstance
  proper _ := inferInstance
  src := D.source
  dst := D.target
  f := D.map
  abelianIndex := id
  group i := (D.abelian i).group
  abelian _ := ⟨inferInstance, inferInstance⟩

structure SpreadFiniteAbelianDiagram
    {K : Type} [Field K] [NumberField K] (D : FiniteAbelianDiagram K) (κ : K →+* ℂ) where
  base : IntegralModel.Base.ArithmeticBaseExtension K κ
  abelian : ∀ i, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (D.dimension i) base.base
  map : ∀ a, (abelian (D.source a)).scheme ⟶ (abelian (D.target a)).scheme
  group : ∀ a, IsMonHom (map a)
  genericIso : ∀ i, (Over.pullback base.generic).obj (abelian i).scheme ≅
    (Over.pullback base.fieldExtension).obj (D.abelian i).scheme
  genericGroup : ∀ i, IsMonHom (genericIso i).hom
  compatible : ∀ a, (Over.pullback base.generic).map (map a) ≫ (genericIso (D.target a)).hom =
    (genericIso (D.source a)).hom ≫ (Over.pullback base.fieldExtension).map (D.map a)

theorem exists_spread_finite_abelian_diagram
    {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ) (D : FiniteAbelianDiagram K)
    (N : ℕ) (hN : N ≠ 0) :
    ∃ M : SpreadFiniteAbelianDiagram D κ, N ∣ M.base.denominator := by
  obtain ⟨B, _, hdiv, X, f, e, groupX, hX, he, hg, _⟩ :=
    IntegralModel.SplitLocalizedModels.exists_split_localized_diagram_model κ D.toFiniteDiagram N hN
  dsimp only [FiniteAbelianDiagram.toFiniteDiagram, id_eq] at X f e groupX hX he hg
  let (i : Fin D.objects) : GrpObj (X i) := groupX i
  let (i : Fin D.objects) : IsCommMonObj (X i) := (hg i).1
  let (i : Fin D.objects) : Smooth (X i).hom := (hX i).1
  let (i : Fin D.objects) : IsProper (X i).hom := (hX i).2.1
  let (i : Fin D.objects) : GeometricallyConnected (X i).hom := (hg i).2.1
  let : IsDomain B.R := Function.Injective.isDomain B.toField B.toField_injective
  let : ConnectedSpace B.base := inferInstanceAs (ConnectedSpace (Spec (.of B.R)))
  let : IsReduced B.base := inferInstanceAs (IsReduced (Spec (.of B.R)))
  let : IsLocallyNoetherian B.base := inferInstanceAs (IsLocallyNoetherian (Spec (.of B.R)))
  let : IsDominant B.generic := B.generic_dominant
  let ec (i : Fin D.objects) : (Over.pullback B.complexPoint).obj (X i) ≅
      ((D.abelian i).pullback (Spec.map (CommRingCat.ofHom κ))).scheme :=
    (Over.pullbackComp (Spec.map (CommRingCat.ofHom B.embedding)) B.generic).app (X i) ≪≫
      (Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))).mapIso (e i) ≪≫
        IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso B (D.abelian i).scheme
  let A (i : Fin D.objects) : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (D.dimension i) B.base :=
    AbelianModelDimension.abelianSchemeOfComplexModel (X i) B.complexPoint
      ((D.abelian i).pullback (Spec.map (CommRingCat.ofHom κ))) (ec i)
  have hf (a : Fin D.arrows) : IsMonHom (f a) := by
    let : IsMonHom (D.map a) := D.group a
    let : IsMonHom (e (D.source a)).hom := (hg (D.source a)).2.2
    let : IsMonHom (e (D.target a)).hom := (hg (D.target a)).2.2
    have hfgen : (Over.pullback B.generic).map (f a) =
        (e (D.source a)).hom ≫ (Over.pullback B.fieldExtension).map (D.map a) ≫
          (e (D.target a)).inv := by
      exact ((e (D.target a)).eq_comp_inv).mpr (he a)
    let : IsMonHom ((Over.pullback B.generic).map (f a)) := by
      rw [hfgen]
      infer_instance
    exact GroupMapReflection.isMonHom_of_dominant_baseChange B.generic (f a)
  exact ⟨{
    base := B
    abelian := A
    map := f
    group := hf
    genericIso := e
    genericGroup := fun i => (hg i).2.2
    compatible := he }, hdiv⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.AbelianDiagramSpreading
