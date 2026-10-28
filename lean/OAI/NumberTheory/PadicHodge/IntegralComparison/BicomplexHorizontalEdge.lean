import OAI.AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge

/-! # Bicomplex Horizontal Edge -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.BicomplexHorizontalEdge

/-! Naturality of the actual zeroth-column augmentation into a total complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C : Type*} [Category C] [Preadditive C]
  (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) [K.HasTotal (.up ℕ)]
  (A : CochainComplex C ℕ) (e : ∀ n, A.X n ⟶ (K.X n).X 0)
  (he : ∀ n n', (ComplexShape.up ℕ).Rel n n' →
    e n ≫ (K.d n n').f 0 = A.d n n' ≫ e n')
  (we : ∀ n, e n ≫ (K.X n).d 0 1 = 0)
  (L : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) [L.HasTotal (.up ℕ)]
  (B : CochainComplex C ℕ) (f : ∀ n, B.X n ⟶ (L.X n).X 0)
  (hf : ∀ n n', (ComplexShape.up ℕ).Rel n n' →
    f n ≫ (L.d n n').f 0 = B.d n n' ≫ f n')
  (wf : ∀ n, f n ≫ (L.X n).d 0 1 = 0)
  (φ : K ⟶ L) (a : A ⟶ B) (h : ∀ n, e n ≫ (φ.f n).f 0 = a.f n ≫ f n)

include h in
theorem naturality : (AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge K) A e he we ≫
    HomologicalComplex₂.total.map φ (.up ℕ) = a ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge L) B f hf wf := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge_f,
    Category.assoc, HomologicalComplex₂.ιTotal_map]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ L.ιTotal (.up ℕ) n 0 n rfl) (h n)).trans
      (Category.assoc _ _ _))

end NumberTheory.PadicHodge.IntegralComparison.BicomplexHorizontalEdge

namespace NumberTheory.PadicHodge.IntegralComparison.BicomplexHorizontalEdge.Precompose

/-! A precomposed horizontal edge is determined by its component on
the zeroth Čech column. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C : Type*} [Category C] [Preadditive C]
  (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) [K.HasTotal (.up ℕ)]
  (A : CochainComplex C ℕ) (e : ∀ n, A.X n ⟶ (K.X n).X 0)
  (he : ∀ n n', (ComplexShape.up ℕ).Rel n n' →
    e n ≫ (K.d n n').f 0 = A.d n n' ≫ e n')
  (we : ∀ n, e n ≫ (K.X n).d 0 1 = 0)
  (L : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) [L.HasTotal (.up ℕ)]
  (B : CochainComplex C ℕ) (f : ∀ n, B.X n ⟶ (L.X n).X 0)
  (hf : ∀ n n', (ComplexShape.up ℕ).Rel n n' →
    f n ≫ (L.d n n').f 0 = B.d n n' ≫ f n')
  (wf : ∀ n, f n ≫ (L.X n).d 0 1 = 0)
  (φ : K ⟶ L) (a : B ⟶ A)
  (h : ∀ n, (a.f n ≫ e n) ≫ (φ.f n).f 0 = f n)

include h in
theorem recovery :
    (a ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge K) A e he we) ≫
      HomologicalComplex₂.total.map φ (.up ℕ) = (AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge L) B f hf wf := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge_f,
    Category.assoc, HomologicalComplex₂.ιTotal_map]
  simpa only [Category.assoc] using
    congrArg (fun g => g ≫ L.ιTotal (.up ℕ) n 0 n rfl) (h n)

end NumberTheory.PadicHodge.IntegralComparison.BicomplexHorizontalEdge.Precompose

end

end OAI
