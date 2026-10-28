import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.ChartTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalConeNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalFunctor

/-! # Chart Total Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.ChartTotalNaturality.SemilatticeChartTotalNaturality

noncomputable section

/-! Canonical chart maps into the original Čech total commute with
subchart restrictions and natural changes of the whole row diagram. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w
variable (C : Type u) [SemilatticeInf C] {ι : Type} (U : ι → C)
  {A : Type v} [Category.{w} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  (I J : C) (hJI : J ≤ I)
  (P Q : Cᵒᵖ ⥤ CochainComplex A ℕ)
  (hP : ∀ V : C, IsIso (P.map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))
  (hQ : ∀ V : C, IsIso (Q.map (homOfLE (inf_le_left : V ⊓ J ≤ V)).op))
  (α : P ⟶ Q)

include hJI in
theorem transition :
    ChartTotal.SemilatticeChartTotal.map C U I P hP ≫ (CechCone.TotalFunctor.CechConeTotalFunctor.functor U).map α =
      (P.map (homOfLE hJI).op ≫ α.app (op J)) ≫ ChartTotal.SemilatticeChartTotal.map C U J Q hQ := by
  exact (CechCone.TotalFunctor.CechConeTotalFunctor.augmentation U (P.obj (op I))
    (LocalCone.SemilatticeLocalCone.cone C I P hP) α).trans
      ((congrArg (fun η => CechCone.Total.CechConeTotal.augmentation U Q (P.obj (op I)) η)
        (LocalConeNaturality.SemilatticeLocalConeNaturality.transition C I P hP J hJI Q hQ α)).trans
          (CechCone.TotalSourceNaturality.CechConeTotalSourceNaturality.augmentation U Q (Q.obj (op J)) (P.obj (op I))
            (LocalCone.SemilatticeLocalCone.cone C J Q hQ) (P.map (homOfLE hJI).op ≫ α.app (op J))).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.ChartTotalNaturality.SemilatticeChartTotalNaturality
