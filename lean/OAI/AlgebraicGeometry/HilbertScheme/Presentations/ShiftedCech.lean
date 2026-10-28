import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ReindexedGrading
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.ExactLeft

/-! # Shifted Cech -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ShiftedCech

noncomputable section

/-! Shifting the grading shifts the internal degree of the actual projective Čech complex. -/

open _root_.MvPolynomial DirectSum

namespace GradedModules

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable (ℳ : ℤ → Submodule R M)

theorem localizedDegreePiece_shifted (a : ℤ) (g : A) (e d : ℤ) :
    Localized.DegreePieces.GradedModules.localizedDegreePiece (ReindexedGrading.GradedModules.shiftedGrading ℳ a) g e d = Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ g e (d + a) := by
  apply iSup_congr
  intro k
  change (ℳ (d + (k : ℤ) * e + a)).map (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) g k) =
    (ℳ (d + a + (k : ℤ) * e)).map (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) g k)
  rw [add_right_comm d ((k : ℤ) * e) a]

end GradedModules

namespace ProjectiveCech

universe u v w

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M)

omit [LinearOrder σ] in
theorem moduleChartDegree_shifted (a d : ℤ) (s : Finset σ) :
    Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M (ReindexedGrading.GradedModules.shiftedGrading ℳ a) s d = Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s (d + a) :=
  GradedModules.localizedDegreePiece_shifted ℳ a (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ) d

omit [LinearOrder σ] in
theorem moduleCechHomogeneous_shifted (a d : ℤ) (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) :
    ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M (ReindexedGrading.GradedModules.shiftedGrading ℳ a) d f ↔ ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ (d + a) f := by
  simp only [ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous, moduleChartDegree_shifted]

theorem moduleCechExactAt_shifted (a d : ℤ) (q : ℕ) :
    Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M (ReindexedGrading.GradedModules.shiftedGrading ℳ a) d q ↔
      Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ (d + a) q := by
  simp only [Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt, moduleCechHomogeneous_shifted]

end ProjectiveCech

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ShiftedCech
