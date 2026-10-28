import OAI.AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees

/-! # Total Complex Zero Coordinates -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexZeroCoordinates

noncomputable section

/-! The two differential coordinates out of total degree zero. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex₂

variable {C : Type*} [Category* C] [Preadditive C]
  (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) [K.HasTotal (.up ℕ)]

theorem total_d_zero_horizontal :
    (K.total (.up ℕ)).d 0 1 ≫ (SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) 0 1 1 =
      (SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) 0 0 0 ≫ (K.X 0).d 0 1 := by
  apply total.hom_ext
  intro q p h
  change q + p = 0 at h
  obtain ⟨rfl, rfl⟩ := Nat.add_eq_zero_iff.mp h
  rw [SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_d_upNat_assoc K 0 0]
  simp

theorem total_d_zero_vertical :
    (K.total (.up ℕ)).d 0 1 ≫ (SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) 1 0 1 =
      (SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) 0 0 0 ≫ (K.d 0 1).f 0 := by
  apply total.hom_ext
  intro q p h
  change q + p = 0 at h
  obtain ⟨rfl, rfl⟩ := Nat.add_eq_zero_iff.mp h
  rw [SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_d_upNat_assoc K 0 0]
  simp

instance total_zero_inclusion_isIso : IsIso (K.ιTotal (.up ℕ) 0 0 0 rfl) :=
  ⟨⟨(SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) 0 0 0, (SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_πTotalUpNat_self K) 0 0, (SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.totalUpNat_zero_decomposition K)⟩⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexZeroCoordinates
