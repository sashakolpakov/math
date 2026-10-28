import OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.RowCoordinates

/-! # Row Injection -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.RowInjection.Coordinates

noncomputable section

/-! Injection normalization for the row-total coordinate isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {A : Type u} [Category.{v} A] [Abelian A] [HasFiniteCoproducts A]
attribute [local instance] Rotation.total Rotation.complexTotal
variable (S : HomologicalComplex₂ (CochainComplex A ℕ) (.up ℕ) (.up ℕ))

def injection (r i j N : ℕ) (h : r+i+j=N) :
    ((S.X i).X j).X r ⟶ ((RowCoordinates.bicomplex S).total (.up ℕ)).X N :=
  (HomologicalComplex₂.flip ((HomologicalComplex₂.flip S).X j)).ιTotal
    (.up ℕ) r i (r+i) rfl ≫ (RowCoordinates.bicomplex S).ιTotal (.up ℕ) (r+i) j N h

@[reassoc]
theorem injection_totalIso (r i j N : ℕ) (h : r+i+j=N) :
    injection S r i j N h ≫ (RowCoordinates.totalIso S).hom.f N =
      Components.leftInjection (Rotation.rotate S) r i j N h := by
  dsimp only [injection, RowCoordinates.totalIso, HomologicalComplex₂.total.mapIso]
  erw [Category.assoc, HomologicalComplex₂.ιTotal_map]
  change (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex (HomologicalComplex.eval A (.up ℕ) j)
    (Rotation.rotate S)).ιTotal (.up ℕ) r i (r+i) rfl ≫
    AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonComponent (HomologicalComplex.eval A (.up ℕ) j)
      (Rotation.rotate S) (r+i) ≫
    (Components.leftBicomplex (Rotation.rotate S)).ιTotal
      (.up ℕ) (r+i) j N h = _
  erw [← Category.assoc, AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.ι_finiteTotalComparisonComponent]
  rfl

@[reassoc]
theorem injection_regroup (r i j N : ℕ) (h : r+i+j=N) :
    RotationInjection.nativeInjection S r i j N h ≫ (RowCoordinates.regroup S).f N =
      injection S r i j N h := by
  dsimp only [RowCoordinates.regroup, HomologicalComplex.comp_f]
  erw [← Category.assoc, RotationInjection.injection_regroup,
    ← injection_totalIso, Category.assoc, ← HomologicalComplex.comp_f,
    Iso.hom_inv_id, HomologicalComplex.id_f, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.RowInjection.Coordinates
