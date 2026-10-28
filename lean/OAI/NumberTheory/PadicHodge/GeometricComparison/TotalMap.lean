import Mathlib.Algebra.Homology.TotalComplex
import OAI.AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees

/-! # Total Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.TotalMap.TotalMapZero

noncomputable section

/-! The original total-complex map sends the zero bicomplex map to zero. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
  (K L : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) [K.HasTotal (.up ℕ)] [L.HasTotal (.up ℕ)]

theorem zero : HomologicalComplex₂.total.map (0 : K ⟶ L) (.up ℕ) = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro i j h
  simp only [HomologicalComplex₂.ιTotal_map, HomologicalComplex.zero_f, zero_comp, comp_zero]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.TotalMap.TotalMapZero
