import OAI.AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexMap
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.TotalComplexSymmetry

/-! # Additive Total Column -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AdditiveTotalColumn

noncomputable section

section

/-! Column quasi-isomorphisms imply a quasi-isomorphism of the actual additive total complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex _root_.HomologicalComplex₂

theorem additive_total_map_quasiIso_of_columns
    {K L : HomologicalComplex₂ AddCommGrpCat.{0} (.up ℕ) (.up ℕ)} (φ : K ⟶ L)
    (hφ : ∀ p : ℕ, QuasiIso (φ.f p)) : QuasiIso (total.map φ (.up ℕ)) := by
  let E := (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}).asEquivalence
  let F := E.inverse
  let : E.functor.Additive := inferInstanceAs (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}).Additive
  let : F.Additive := E.inverse_additive
  let : F.PreservesHomology := inferInstance
  let : F.ReflectsIsomorphisms := inferInstance
  let ψ := TotalAdditiveFunctor.mapBicomplexMap F φ
  have hψ (p : ℕ) : QuasiIso (ψ.f p) :=
    quasiIso_map_of_preservesHomology (φ.f p) F (hφ := hφ p)
  have ht : QuasiIso (total.map ψ (.up ℕ)) :=
    AlgebraicTopology.DeRham.Comparison.DoubleComplexMap.DoubleComplex.total_map_quasiIso_of_columns ψ hψ
  let A := TotalAdditiveFunctor.totalComparisonIsoOfAdditive F K
  let B := TotalAdditiveFunctor.totalComparisonIsoOfAdditive F L
  let g := (F.mapHomologicalComplex (.up ℕ)).map (total.map φ (.up ℕ))
  have h : total.map ψ (.up ℕ) ≫ B.hom = A.hom ≫ g := TotalAdditiveFunctor.totalComparison_naturality F φ
  have hA : QuasiIso A.hom := quasiIso_of_isIso A.hom
  have hB : QuasiIso B.hom := quasiIso_of_isIso B.hom
  have hc : QuasiIso (A.hom ≫ g) := by
    rw [← h]
    exact quasiIso_comp (total.map ψ (.up ℕ)) B.hom (hφ := ht) (hφ' := hB)
  have hg : QuasiIso g := quasiIso_of_comp_left A.hom g (hφ := hA) (hφφ' := hc)
  exact (quasiIso_map_iff_of_preservesHomology (total.map φ (.up ℕ)) F).mp hg

end

/-! The interchange sign is natural for actual first-quadrant bicomplex maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex₂

variable {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{0} C]
  {K L : HomologicalComplex₂ C (.up ℕ) (.up ℕ)} (φ : K ⟶ L)

theorem totalFlipIso_naturality :
    total.map ((flipFunctor C (.up ℕ) (.up ℕ)).map φ) (.up ℕ) ≫ (L.totalFlipIso (.up ℕ)).hom =
      (K.totalFlipIso (.up ℕ)).hom ≫ total.map φ (.up ℕ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply total.hom_ext
  intro p q h
  change K.flip.ιTotal (.up ℕ) p q n h ≫
      ((total.map ((flipFunctor C (.up ℕ) (.up ℕ)).map φ) (.up ℕ)).f n ≫
        (L.totalFlipIso (.up ℕ)).hom.f n) =
    K.flip.ιTotal (.up ℕ) p q n h ≫
      ((K.totalFlipIso (.up ℕ)).hom.f n ≫ (total.map φ (.up ℕ)).f n)
  erw [← Category.assoc, ιTotal_map, Category.assoc, ιTotal_totalFlipIso_f_hom,
    ← Category.assoc, ιTotal_totalFlipIso_f_hom, Linear.comp_units_smul, Linear.units_smul_comp,
    ιTotal_map]
  rfl

theorem additive_total_map_quasiIso_of_rows
    {K L : HomologicalComplex₂ AddCommGrpCat.{0} (.up ℕ) (.up ℕ)} (φ : K ⟶ L)
    (hφ : ∀ p, QuasiIso (((flipFunctor AddCommGrpCat (.up ℕ) (.up ℕ)).map φ).f p)) :
    QuasiIso (total.map φ (.up ℕ)) := by
  let ψ := (flipFunctor AddCommGrpCat (.up ℕ) (.up ℕ)).map φ
  have hψ : QuasiIso (total.map ψ (.up ℕ)) := additive_total_map_quasiIso_of_columns ψ hφ
  have hK : QuasiIso (K.totalFlipIso (.up ℕ)).hom := quasiIso_of_isIso _
  have hL : QuasiIso (L.totalFlipIso (.up ℕ)).hom := quasiIso_of_isIso _
  have hc : QuasiIso ((K.totalFlipIso (.up ℕ)).hom ≫ total.map φ (.up ℕ)) := by
    rw [← totalFlipIso_naturality φ]
    exact quasiIso_comp (total.map ψ (.up ℕ)) (L.totalFlipIso (.up ℕ)).hom (hφ := hψ) (hφ' := hL)
  exact quasiIso_of_comp_left (K.totalFlipIso (.up ℕ)).hom (total.map φ (.up ℕ))
    (hφ := hK) (hφφ' := hc)

end

end OAI.AlgebraicGeometry.Comparison.Betti.AdditiveTotalColumn
