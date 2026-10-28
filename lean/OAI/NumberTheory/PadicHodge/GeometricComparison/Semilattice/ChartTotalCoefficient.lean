import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.ChartTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalAugmentationNaturality

/-! # Chart Total Coefficient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.ChartTotalCoefficient.SemilatticeChartTotalCoefficient

noncomputable section

/-! Every additive module-valued functor preserves the canonical
quasi-isomorphism from a chart coefficient to its finite Čech total. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w z t
variable (C : Type u) [SemilatticeInf C] (I : C)
  {A : Type v} [Category.{w} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  (R : Type z) [CommRing R] (F : A ⥤ ModuleCat.{max z t} R) [F.Additive]
  (P : Cᵒᵖ ⥤ CochainComplex A ℕ)
  (h : ∀ V : C, IsIso (P.map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))

omit [HasProducts.{0} A] [HasCoproducts.{0} A] in
include h in
theorem mapped_meet (V : C) : IsIso
    ((CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped F P).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op) := by
  let := h V
  change IsIso ((F.mapHomologicalComplex (.up ℕ)).map (P.map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))
  infer_instance

omit [HasProducts.{0} A] [HasCoproducts.{0} A] in
theorem mapped_chart : QuasiIso
    ((CechCone.TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone F P (P.obj (op I))
      (LocalCone.SemilatticeLocalCone.cone C I P h)).app (op I)) := by
  rw [CechCone.TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone_app]
  let : IsIso ((LocalCone.SemilatticeLocalCone.cone C I P h).app (op I)) :=
    (LocalCone.SemilatticeLocalCone.self C I P h).symm ▸ (inferInstanceAs (IsIso (𝟙 (P.obj (op I)))))
  exact inferInstanceAs (QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map
    ((LocalCone.SemilatticeLocalCone.cone C I P h).app (op I))))

variable {ι : Type} [Finite ι] (U : ι → C) (i : ι) (hi : I ≤ U i)

include hi in
theorem quasiIso : QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map
    (ChartTotal.SemilatticeChartTotal.map C U I P h)) := by
  apply (quasiIso_iff_comp_right _ (CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso F U P).hom).mp
  change QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map
    (CechCone.Total.CechConeTotal.augmentation U P (P.obj (op I)) (LocalCone.SemilatticeLocalCone.cone C I P h)) ≫
      (CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso F U P).hom)
  rw [CechCone.TotalAugmentationNaturality.CechConeTotalAugmentationNaturality.augmentation]
  exact @SubchartModuleCechTotal.SemilatticeSubchartModuleCechTotal.quasiIso R _ C _ _ U I i hi
    (CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped F P) (fun V => mapped_meet C I R F P h V)
    ((F.mapHomologicalComplex (.up ℕ)).obj (P.obj (op I)))
    (CechCone.TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone F P (P.obj (op I)) (LocalCone.SemilatticeLocalCone.cone C I P h))
    (mapped_chart C I R F P h)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.ChartTotalCoefficient.SemilatticeChartTotalCoefficient
