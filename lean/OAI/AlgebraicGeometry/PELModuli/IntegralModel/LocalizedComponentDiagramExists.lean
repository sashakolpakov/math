import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComponentFiniteDiagram
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ModelComplexComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SplitLocalizedModels
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SplitGenericConnectedness

/-! # Localized Component Diagram Exists -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LocalizedComponentDiagramExists

noncomputable section

/-! Construct the localized arithmetic diagram of component sources,
abelian targets, point arrows and maps, retaining all complex comparisons. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

structure LocalizedComponentDiagram
    {K : Type} [Field K] [NumberField K] {T : Over (Spec (.of K))} {r : ℕ}
    (D : Components.ComponentAlbaneseData T r) (κ : K →+* ℂ) where
  base : Base.ArithmeticBaseExtension K κ
  unitModel : Over base.base
  source : Fin r → Over base.base
  target : Fin r → CommGrp (Over base.base)
  point : ∀ i, unitModel ⟶ source i
  map : ∀ i, source i ⟶ (target i).X
  unitIso : (Over.pullback base.complexPoint).obj unitModel ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj (𝟙_ (Over (Spec (.of K))))
  sourceIso : ∀ i, (Over.pullback base.complexPoint).obj (source i) ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj (D.S i)
  targetIso : ∀ i, (Over.pullback base.complexPoint).obj (target i).X ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj (D.A i).X
  targetGroup : ∀ i, IsMonHom (targetIso i).hom
  unitGeometry : Smooth unitModel.hom ∧ IsProper unitModel.hom
  sourceGeometry : ∀ i, Smooth (source i).hom ∧ IsProper (source i).hom ∧ GeometricallyConnected (source i).hom
  targetGeometry : ∀ i, Smooth (target i).X.hom ∧ IsProper (target i).X.hom ∧ GeometricallyConnected (target i).X.hom
  pointComparison : ∀ i, (Over.pullback base.complexPoint).map (point i) ≫ (sourceIso i).hom =
    unitIso.hom ≫ (Over.pullback (Spec.map (CommRingCat.ofHom κ))).map (D.x₀ i)
  mapComparison : ∀ i, (Over.pullback base.complexPoint).map (map i) ≫ (targetIso i).hom =
    (sourceIso i).hom ≫ (Over.pullback (Spec.map (CommRingCat.ofHom κ))).map (D.a i)

theorem localized_component_diagram_exists
    {K : Type} [Field K] [NumberField K] {T : Over (Spec (.of K))} {r : ℕ}
    (D : Components.ComponentAlbaneseData T r) (κ : K →+* ℂ)
    (hS : ∀ i, Smooth (D.S i).hom ∧ IsProper (D.S i).hom ∧ GeometricallyConnected (D.S i).hom)
    (hA : ∀ i, Smooth (D.A i).X.hom ∧ IsProper (D.A i).X.hom ∧ GeometricallyConnected (D.A i).X.hom)
    (N : ℕ) (hN : N ≠ 0) :
    ∃ W : LocalizedComponentDiagram D κ, IsUnit (N : W.base.R) ∧ N ∣ W.base.denominator := by
  let Δ := ComponentFiniteDiagram.componentFiniteDiagram D (fun i => ⟨(hS i).1, (hS i).2.1⟩) hA
  obtain ⟨B, hNB, hdiv, M, f, e, groupM, hM, he, hg, _⟩ :=
    SplitLocalizedModels.exists_split_localized_diagram_model κ Δ N hN
  let A (i : Fin r) : CommGrp (Over B.base) := by
    let : GrpObj (M (some (.inr i))) := groupM i
    exact { X := M (some (.inr i)), comm := (hg i).1 }
  have hs (i : Fin r) : GeometricallyConnected (M (some (.inl i))).hom := by
    have : Smooth (M (some (.inl i))).hom := (hM (some (.inl i))).1
    have : IsProper (M (some (.inl i))).hom := (hM (some (.inl i))).2.1
    have : GeometricallyConnected (D.S i).hom := (hS i).2.2
    have hfield : GeometricallyConnected ((Over.pullback B.fieldExtension).obj (D.S i)).hom :=
      inferInstanceAs (GeometricallyConnected (CategoryTheory.Limits.pullback.snd (D.S i).hom B.fieldExtension))
    have : GeometricallyConnected ((Over.pullback B.generic).obj (M (some (.inl i)))).hom :=
      SplitGenericConnectedness.geometricallyConnected_of_over_iso (e (some (.inl i))) hfield
    exact B.split_model_geometricallyConnected _ (hM (some (.inl i))).2.2
  let W : LocalizedComponentDiagram D κ := {
    base := B
    unitModel := M none
    source := fun i => M (some (.inl i))
    target := A
    point := fun i => f (.inl i)
    map := fun i => f (.inr i)
    unitIso := Arithmetic.ModelComplexComparison.arithmeticModelComplexComparison B _ _ (e none)
    sourceIso := fun i => Arithmetic.ModelComplexComparison.arithmeticModelComplexComparison B _ _ (e (some (.inl i)))
    targetIso := fun i => Arithmetic.ModelComplexComparison.arithmeticModelComplexComparison B _ _ (e (some (.inr i)))
    targetGroup := fun i => by
      let : GrpObj (M (some (.inr i))) := groupM i
      let : GrpObj (Δ.X (some (.inr i))) := (D.A i).grp
      let : GrpObj ((Over.pullback B.generic).obj (M (some (.inr i)))) := Functor.grpObjObj
      let : GrpObj ((Over.pullback B.fieldExtension).obj (Δ.X (some (.inr i)))) := Functor.grpObjObj
      have : IsMonHom (e (some (.inr i))).hom := (hg i).2.2
      exact Arithmetic.ModelComplexComparison.arithmeticModelComplexComparison_isMonHom B _ _ (e (some (.inr i)))
    unitGeometry := ⟨(hM none).1, (hM none).2.1⟩
    sourceGeometry := fun i => ⟨(hM (some (.inl i))).1, (hM (some (.inl i))).2.1, hs i⟩
    targetGeometry := fun i => ⟨(hM (some (.inr i))).1, (hM (some (.inr i))).2.1, (hg i).2.1⟩
    pointComparison := fun i => Arithmetic.ModelComplexComparison.arithmeticModelComplexComparison_compatible B _ _
      (f (.inl i)) (D.x₀ i) (he (.inl i))
    mapComparison := fun i => Arithmetic.ModelComplexComparison.arithmeticModelComplexComparison_compatible B _ _
      (f (.inr i)) (D.a i) (he (.inr i)) }
  exact ⟨W, hNB, hdiv⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LocalizedComponentDiagramExists
