import OAI.AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees

/-! # Total Projection Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TotalProjectionNaturality

noncomputable section

/-! The actual projection to a bidegree commutes with maps of
first-quadrant total complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K L : HomologicalComplex₂ C (.up ℕ) (.up ℕ)}
  [K.HasTotal (.up ℕ)] [L.HasTotal (.up ℕ)]

@[reassoc]
theorem map (f : K ⟶ L) (p q n : ℕ) :
    (HomologicalComplex₂.total.map f (.up ℕ)).f n ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat L) p q n =
      (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) p q n ≫ (f.f p).f q := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  rw [HomologicalComplex₂.ιTotal_map_assoc, AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_πTotalUpNat_assoc,
    AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_πTotalUpNat]
  by_cases ha : a = p
  · subst a
    by_cases hb : b = q
    · subst b
      simp [HomologicalComplex₂.XXIsoOfEq]
    · simp [hb]
  · simp [ha]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TotalProjectionNaturality
