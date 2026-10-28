import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso

/-! # Cone Diagram Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConeDiagramQuasiIso

noncomputable section

/-! The original complex-valued Čech total preserves genuine local
quasi-isomorphisms on every nonempty intersection. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v r s
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  (R : Type r) [CommRing R] {ι : Type} [Finite ι] (U : ι → C)
  {P Q : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{max r s} R) ℕ} (a : P ⟶ Q)
  (ha : ∀ (j : ℕ) (b : Fin (j+1) → ι), QuasiIso (a.app (op (∏ᶜ (U ∘ b)))))

include ha in
theorem quasiIso : QuasiIso ((GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.functor U).map a) := by
  have ht : QuasiIso (ComplexDiagramNaturality.Coordinates.totalMap U a) :=
    AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.quasiIso R (NonemptyCechNerve.nerve U)
      (ComplexDiagramNaturality.Coordinates.complexMap a) ha
  have hc : QuasiIso ((GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.functor U).map a ≫
      (ComplexDiagramCoordinates.totalIso U Q).hom) := by
    rw [ComplexDiagramNaturality.Coordinates.total_natural]
    exact quasiIso_comp (ComplexDiagramCoordinates.totalIso U P).hom
      (ComplexDiagramNaturality.Coordinates.totalMap U a) (hφ' := ht)
  exact (quasiIso_iff_comp_right _ (ComplexDiagramCoordinates.totalIso U Q).hom).mp hc

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConeDiagramQuasiIso
