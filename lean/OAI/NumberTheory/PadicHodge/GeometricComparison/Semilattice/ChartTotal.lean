import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalCone
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalSourceNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.SubchartModuleCechTotal

/-! # Chart Total -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.ChartTotal.SemilatticeChartTotal

noncomputable section

/-! The canonical chart-to-total map factors every original augmentation.
It is a quasi-isomorphism for module coefficients on a covered subchart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

section

universe u v w z
variable (C : Type u) [SemilatticeInf C] {ι : Type} (U : ι → C) (I : C)
  {A : Type v} [Category.{w} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  (P : Cᵒᵖ ⥤ CochainComplex A ℕ)
  (h : ∀ V : C, IsIso (P.map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))

def map : P.obj (op I) ⟶ CechCone.Total.CechConeTotal.total U P :=
  CechCone.Total.CechConeTotal.augmentation U P (P.obj (op I)) (LocalCone.SemilatticeLocalCone.cone C I P h)

theorem factorization (M : CochainComplex A ℕ) (η : (Functor.const Cᵒᵖ).obj M ⟶ P) :
    CechCone.Total.CechConeTotal.augmentation U P M η = η.app (op I) ≫ SemilatticeChartTotal.map C U I P h := by
  have hη := LocalCone.SemilatticeLocalCone.factorization C I P h M η
  exact (congrArg (fun θ => CechCone.Total.CechConeTotal.augmentation U P M θ) hη).trans
    (CechCone.TotalSourceNaturality.CechConeTotalSourceNaturality.augmentation U P (P.obj (op I)) M
      (LocalCone.SemilatticeLocalCone.cone C I P h) (η.app (op I))).symm

end

universe u v w
variable (R : Type u) [CommRing R] (C : Type v) [SemilatticeInf C]
  {ι : Type} (U : ι → C) (I : C) (i : ι) (hi : I ≤ U i)
  (P : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{max u w} R) ℕ)
  (h : ∀ V : C, IsIso (P.map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))

include hi in
theorem quasiIso : QuasiIso (SemilatticeChartTotal.map C U I P h) := by
  have hself : QuasiIso ((LocalCone.SemilatticeLocalCone.cone C I P h).app (op I)) := by
    exact (LocalCone.SemilatticeLocalCone.self C I P h).symm ▸ (inferInstanceAs (QuasiIso (𝟙 (P.obj (op I)))))
  exact @SubchartModuleCechTotal.SemilatticeSubchartModuleCechTotal.quasiIso R _ C _ _ U I i hi P h
    (P.obj (op I)) (LocalCone.SemilatticeLocalCone.cone C I P h) hself

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.ChartTotal.SemilatticeChartTotal
