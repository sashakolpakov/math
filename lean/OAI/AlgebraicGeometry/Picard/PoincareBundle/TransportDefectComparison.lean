import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.IsoRatios

/-! # Transport Defect Comparison -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TransportDefectComparison

noncomputable section

/-! Changing actual line transports changes their defect by the ratios of the three edges. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.IsoRatios

variable {X : Scheme.{u}} {M N P : X.Modules}

/-- The comparison is an identity between coefficients of actual line isomorphisms. -/
theorem compare (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) (hN : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle N)
    (e e' : M ≅ N) (f f' : N ≅ P) (g g' : M ≅ P) :
    Line.IsoRatios.ratio hM (e ≪≫ f) g * Line.IsoRatios.ratio hM g g' =
      Line.IsoRatios.ratio hM e e' * Line.IsoRatios.ratio hN f f' * Line.IsoRatios.ratio hM (e' ≪≫ f') g' := by
  have h₁ := Line.IsoRatios.ratio_chain hM (e ≪≫ f) g g'
  have h₂ := Line.IsoRatios.ratio_chain hM (e ≪≫ f) (e' ≪≫ f') g'
  rw [Line.IsoRatios.ratio_comp hM hN] at h₂
  exact h₁.trans h₂.symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TransportDefectComparison
