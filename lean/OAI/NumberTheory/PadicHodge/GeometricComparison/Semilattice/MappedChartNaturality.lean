import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.MappedChartTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.ChartTotalNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.CoefficientComposition
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.CoefficientTransformation

/-! # Mapped Chart Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.MappedChartNaturality.SemilatticeMappedChartNaturality

noncomputable section

/-! The canonical restricted chart map commutes with further
coefficient functors and with natural coefficient isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z t x y
variable (C : Type u) [SemilatticeInf C] {ι : Type} [Finite ι]
  (U : ι → C) (V : C)
  {A : Type v} [Category.{w} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type z} [Category.{t} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  (F : A ⥤ B) [F.Additive] (P : Cᵒᵖ ⥤ CochainComplex A ℕ)
  (hF : ∀ T : C, IsIso ((F.mapHomologicalComplex (.up ℕ)).map
    (P.map (homOfLE (inf_le_left : T ⊓ V ≤ T)).op)))

theorem cone_factorization (M : CochainComplex B ℕ)
    (η : (Functor.const Cᵒᵖ).obj M ⟶ CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped F P) :
    CechCone.Total.CechConeTotal.augmentation U (CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped F P) M η ≫
        (CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso F U P).inv =
      η.app (op V) ≫ MappedChartTotal.SemilatticeMappedChartTotal.map C U V F P hF := by
  rw [ChartTotal.SemilatticeChartTotal.factorization C U V _ hF M η]
  exact Category.assoc _ _ _

variable {D : Type x} [Category.{y} D] [Abelian D]
  [HasProducts.{0} D] [HasCoproducts.{0} D] (G : B ⥤ D) [G.Additive]

theorem composition
    (hFG : ∀ T : C, IsIso (((F ⋙ G).mapHomologicalComplex (.up ℕ)).map
      (P.map (homOfLE (inf_le_left : T ⊓ V ≤ T)).op))) :
    (G.mapHomologicalComplex (.up ℕ)).map (MappedChartTotal.SemilatticeMappedChartTotal.map C U V F P hF) =
      MappedChartTotal.SemilatticeMappedChartTotal.map C U V (F ⋙ G) P hFG := by
  let Q := CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped F P
  let θ := LocalCone.SemilatticeLocalCone.cone C V Q hF
  have hc := LocalConeNaturality.SemilatticeLocalConeNaturality.functor_naturality C V Q hF
    (G.mapHomologicalComplex (.up ℕ)) hFG
  have ha := CechCone.TotalAugmentationNaturality.CechConeTotalAugmentationNaturality.augmentation G U Q (Q.obj (op V)) θ
  have hcone : CechCone.TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone G Q (Q.obj (op V)) θ =
      LocalCone.SemilatticeLocalCone.cone C V (CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped (F ⋙ G) P) hFG := hc
  rw [hcone] at ha
  have he : CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso (F ⋙ G) U P =
      (G.mapHomologicalComplex (.up ℕ)).mapIso (CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso F U P) ≪≫
        CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso G U Q :=
    Iso.ext (CechCone.CoefficientComposition.CechConeCoefficientComposition.total F G U P)
  have hi := congrArg Iso.inv he
  have hchart : (G.mapHomologicalComplex (.up ℕ)).map (ChartTotal.SemilatticeChartTotal.map C U V Q hF) =
      ChartTotal.SemilatticeChartTotal.map C U V (CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped (F ⋙ G) P) hFG ≫
        (CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso G U Q).inv :=
    (CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso G U Q).eq_comp_inv.mpr ha
  change (G.mapHomologicalComplex (.up ℕ)).map
      (ChartTotal.SemilatticeChartTotal.map C U V Q hF ≫ (CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso F U P).inv) =
    ChartTotal.SemilatticeChartTotal.map C U V (CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped (F ⋙ G) P) hFG ≫
      (CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso (F ⋙ G) U P).inv
  rw [CategoryTheory.Functor.map_comp, hchart, hi]
  exact Category.assoc _ _ _

theorem iso (G : A ⥤ B) [G.Additive] (e : F ≅ G)
    (hG : ∀ T : C, IsIso ((G.mapHomologicalComplex (.up ℕ)).map
      (P.map (homOfLE (inf_le_left : T ⊓ V ≤ T)).op))) :
    MappedChartTotal.SemilatticeMappedChartTotal.map C U V F P hF ≫
        ((NatIso.mapHomologicalComplex e (.up ℕ)).app (CechCone.Total.CechConeTotal.total U P)).hom =
      ((NatIso.mapHomologicalComplex e (.up ℕ)).app (P.obj (op V))).hom ≫
        MappedChartTotal.SemilatticeMappedChartTotal.map C U V G P hG := by
  let α := Functor.whiskerLeft P (e.hom.mapHomologicalComplex (.up ℕ))
  have hchart := ChartTotalNaturality.SemilatticeChartTotalNaturality.transition C U V V le_rfl
    (CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped F P) (CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped G P) hF hG α
  have hid : (CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped F P).map (homOfLE (le_refl V)).op = 𝟙 _ :=
    (CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped F P).map_id (op V)
  rw [hid, Category.id_comp] at hchart
  have ht := CechCone.CoefficientTransformation.CechConeCoefficientTransformation.total F G e.hom U P
  apply (cancel_mono (CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso G U P).hom).mp
  change ((ChartTotal.SemilatticeChartTotal.map C U V (CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped F P) hF ≫
      (CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso F U P).inv) ≫
        (e.hom.mapHomologicalComplex (.up ℕ)).app (CechCone.Total.CechConeTotal.total U P)) ≫
          (CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso G U P).hom =
    ((e.hom.mapHomologicalComplex (.up ℕ)).app (P.obj (op V)) ≫
      (ChartTotal.SemilatticeChartTotal.map C U V (CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped G P) hG ≫
        (CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso G U P).inv)) ≫
          (CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso G U P).hom
  simp only [Category.assoc]
  rw [ht]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  exact hchart

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.MappedChartNaturality.SemilatticeMappedChartNaturality
