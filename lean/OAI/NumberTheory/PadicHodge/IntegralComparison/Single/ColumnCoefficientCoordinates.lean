import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ColumnCycleCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.HomologyCoefficient
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison

/-! # Column Coefficient Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ColumnCoefficientCoordinates

noncomputable section

/-! Exact coefficient change preserves the original signed
single-column homology coordinate of a nonnegative total. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
open OAI.NumberTheory.PadicHodge.IntegralComparison.AbelianSingleRowTotal OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ColumnCycleCoordinates
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{0} C]
  {D : Type w} [Category.{z} D] [Abelian D] [HasCoproducts.{0} D]
  (G : C ⥤ D) [G.Additive] [G.PreservesHomology]
  (B : HomologicalComplex₂ C (.up ℕ) (.up ℕ))

local instance finiteBiproducts : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts

abbrev mapped := AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex G B
abbrev totalIso := AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G B

omit [G.PreservesHomology] in
theorem projection (p q n : ℕ) (h : p+q=n) :
    (totalIso G B).hom.f n ≫ G.map (AbelianSingleRowTotal.projection B p q n h) =
      AbelianSingleRowTotal.projection (mapped G B) p q n h := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  rw [← Category.assoc]
  change ((mapped G B).ιTotal (.up ℕ) a b n hab ≫ AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparisonComponent G B n) ≫ _ = _
  rw [AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.ι_totalComparisonComponent, ← G.map_comp]
  by_cases ha : a = p
  · subst a
    by_cases hb : b = q
    · subst b
      simp [AbelianSingleRowTotal.projection]
      rfl
    · simp [AbelianSingleRowTotal.projection, hb]
  · simp [AbelianSingleRowTotal.projection, ha]

omit [G.PreservesHomology] in
theorem inverse_projection (p q n : ℕ) (h : p+q=n) :
    (totalIso G B).inv.f n ≫ AbelianSingleRowTotal.projection (mapped G B) p q n h =
      G.map (AbelianSingleRowTotal.projection B p q n h) := by
  apply (cancel_epi ((totalIso G B).hom.f n)).mp
  rw [← Category.assoc, ← comp_f, Iso.hom_inv_id, id_f, Category.id_comp]
  exact (projection G B p q n h).symm

variable (c : ℕ) (hB : ∀ p q, q ≠ c → IsZero ((B.flip.X p).X q))

include hB in
omit [HasCoproducts C] [HasCoproducts D] [G.PreservesHomology] in
theorem support (p q : ℕ) (hq : q ≠ c) : IsZero (((mapped G B).flip.X p).X q) :=
  G.map_isZero (hB p q hq)

theorem cycle (n : ℕ) :
    cyclesMap (totalIso G B).inv (n+c) ≫
        ColumnCycleCoordinates.cycleProjection (mapped G B) c (support G B c hB) n ≫
          (((B.X c).sc n).mapCyclesIso G).hom =
      ((((B.total (.up ℕ)).sc (n+c)).mapCyclesIso G).hom) ≫
        G.map (ColumnCycleCoordinates.cycleProjection B c hB n) := by
  let T := (G.mapHomologicalComplex (.up ℕ)).obj (B.total (.up ℕ))
  let R := (G.mapHomologicalComplex (.up ℕ)).obj (B.X c)
  have hr : (((B.X c).sc n).mapCyclesIso G).hom ≫ G.map ((B.X c).iCycles n) = R.iCycles n :=
    ShortComplex.mapCyclesIso_hom_iCycles ((B.X c).sc n) G
  have ht : ((((B.total (.up ℕ)).sc (n+c)).mapCyclesIso G).hom) ≫
      G.map ((B.total (.up ℕ)).iCycles (n+c)) = T.iCycles (n+c) :=
    ShortComplex.mapCyclesIso_hom_iCycles ((B.total (.up ℕ)).sc (n+c)) G
  apply (cancel_mono (G.map ((B.X c).iCycles n))).mp
  calc
    _ = cyclesMap (totalIso G B).inv (n+c) ≫
        (ColumnCycleCoordinates.cycleProjection (mapped G B) c (support G B c hB) n ≫ R.iCycles n) := by
      simp only [Category.assoc, hr]
    _ = cyclesMap (totalIso G B).inv (n+c) ≫
        ((mapped G B).total (.up ℕ)).iCycles (n+c) ≫
          (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) c n •
            AbelianSingleRowTotal.projection (mapped G B) c n (n+c) (by omega)) := by
      erw [ColumnCycleCoordinates.cycleProjection_i]
    _ = T.iCycles (n+c) ≫ ((totalIso G B).inv.f (n+c) ≫
        (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) c n •
          AbelianSingleRowTotal.projection (mapped G B) c n (n+c) (by omega))) := by
      rw [← Category.assoc, cyclesMap_i, Category.assoc]
    _ = T.iCycles (n+c) ≫ G.map
        (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) c n •
          AbelianSingleRowTotal.projection B c n (n+c) (by omega)) := by
      erw [Preadditive.comp_zsmul, inverse_projection, G.map_zsmul]
    _ = _ := by
      rw [Category.assoc, ← G.map_comp, ColumnCycleCoordinates.cycleProjection_i, G.map_comp, ← Category.assoc, ht]

theorem homology (n : ℕ) :
    homologyMap (totalIso G B).inv (n+c) ≫
        (ColumnCycleCoordinates.homologyIso (mapped G B) c (support G B c hB) n).hom ≫
          (((B.X c).sc n).mapHomologyIso G).hom =
      ((((B.total (.up ℕ)).sc (n+c)).mapHomologyIso G).hom) ≫
        G.map (ColumnCycleCoordinates.homologyIso B c hB n).hom := by
  let T := (G.mapHomologicalComplex (.up ℕ)).obj (B.total (.up ℕ))
  have hr := HomologyCoefficient.homology_coordinate G ((B.X c).sc n)
  have ht := HomologyCoefficient.homology_coordinate G ((B.total (.up ℕ)).sc (n+c))
  have hc := congrArg (fun a => a ≫ (((B.X c).sc n).mapHomologyIso G).hom)
    (ColumnCycleCoordinates.homologyπ_coordinate (mapped G B) c (support G B c hB) n)
  simp only [Category.assoc] at hc
  have hcyc := cycle G B c hB n
  simp only [← Category.assoc] at hcyc
  apply (cancel_epi (T.homologyπ (n+c))).mp
  simp only [← Category.assoc]
  erw [homologyπ_naturality]
  simp only [Category.assoc]
  erw [hc, hr]
  simp only [← Category.assoc]
  erw [hcyc]
  simp only [Category.assoc]
  erw [← G.map_comp, ← ColumnCycleCoordinates.homologyπ_coordinate, G.map_comp]
  simp only [← Category.assoc]
  erw [ht]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ColumnCoefficientCoordinates
