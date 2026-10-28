import OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.Rotation

/-! # Rotation Injection -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.RotationInjection

noncomputable section

/-! The native regrouping preserves each actual form/Čech/Čech
coproduct injection, without a sign or a reindexing premise. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {A : Type u} [Category.{v} A] [Abelian A] [HasFiniteCoproducts A]
attribute [local instance] Rotation.total Rotation.complexTotal
variable (S : HomologicalComplex₂ (CochainComplex A ℕ) (.up ℕ) (.up ℕ))

def nativeInjection (r i j N : ℕ) (h : r+i+j=N) :
    ((S.X i).X j).X r ⟶ ((HomologicalComplex₂.flip (S.total (.up ℕ))).total (.up ℕ)).X N :=
  (S.ιTotal (.up ℕ) i j (i+j) rfl).f r ≫
    (HomologicalComplex₂.flip (S.total (.up ℕ))).ιTotal (.up ℕ) r (i+j) N (by change r+(i+j)=N; omega)

@[reassoc]
theorem rightInjection_totalIso (r i j N : ℕ) (h : r+i+j=N) :
    Components.rightInjection (Rotation.rotate S) r i j N h ≫ (Rotation.totalIso S).hom.f N =
      nativeInjection S r i j N h := by
  dsimp only [Components.rightInjection, Rotation.totalIso, Rotation.bicomplexIso,
    HomologicalComplex₂.total.mapIso]
  erw [Category.assoc, HomologicalComplex₂.ιTotal_map]
  change HomologicalComplex₂.ιTotal
    (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex (HomologicalComplex.eval A (.up ℕ) r) S)
      (.up ℕ) i j (i+j) rfl ≫
    AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonComponent (HomologicalComplex.eval A (.up ℕ) r) S (i+j) ≫
    (HomologicalComplex₂.flip (S.total (.up ℕ))).ιTotal (.up ℕ) r (i+j) N _ = _
  erw [← Category.assoc, AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.ι_finiteTotalComparisonComponent]
  rfl

@[reassoc]
theorem injection_regroup (r i j N : ℕ) (h : r+i+j=N) :
    nativeInjection S r i j N h ≫ (Rotation.regroup S).f N =
      Components.leftInjection (Rotation.rotate S) r i j N h := by
  rw [← rightInjection_totalIso]
  dsimp only [Rotation.regroup, HomologicalComplex.comp_f]
  erw [Category.assoc, ← Category.assoc ((Rotation.totalIso S).hom.f N),
    ← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f,
    Category.id_comp]
  exact Association.injection (Rotation.rotate S) r i j N h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.RotationInjection
