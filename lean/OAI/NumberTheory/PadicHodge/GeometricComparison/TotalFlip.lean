import OAI.AlgebraicGeometry.SheafCohomology.Cech.TotalComplexUpNat
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Total Flip -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.TotalFlip.TotalFlipNaturality

noncomputable section

/-! Naturality of the original signed total-flip isomorphism. -/

open _root_.CategoryTheory

universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]
  {B C : HomologicalComplex₂ A (.up ℕ) (.up ℕ)}
  [B.HasTotal (.up ℕ)] [C.HasTotal (.up ℕ)] (f : B ⟶ C)

def flipped : B.flip ⟶ C.flip := (HomologicalComplex₂.flipFunctor A (.up ℕ) (.up ℕ)).map f

theorem natural :
    HomologicalComplex₂.total.map (flipped f) (.up ℕ) ≫ (C.totalFlipIso (.up ℕ)).hom =
      (B.totalFlipIso (.up ℕ)).hom ≫ HomologicalComplex₂.total.map f (.up ℕ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro q p h
  change B.flip.ιTotal (.up ℕ) q p n h ≫
      (HomologicalComplex₂.total.map (flipped f) (.up ℕ)).f n ≫
        (C.totalFlipIso (.up ℕ)).hom.f n =
    B.flip.ιTotal (.up ℕ) q p n h ≫ (B.totalFlipIso (.up ℕ)).hom.f n ≫
      (HomologicalComplex₂.total.map f (.up ℕ)).f n
  rw [HomologicalComplex₂.ιTotal_map_assoc B.flip C.flip (flipped f),
    B.ιTotal_totalFlipIso_f_hom_assoc]
  rw [C.ιTotal_totalFlipIso_f_hom]
  have hpq : p + q = n := by change q + p = n at h; omega
  change (f.f p).f q ≫ (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) p q •
      C.ιTotal (.up ℕ) p q n hpq) =
    (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) p q • B.ιTotal (.up ℕ) p q n hpq) ≫
      (HomologicalComplex₂.total.map f (.up ℕ)).f n
  rw [Linear.comp_units_smul, Linear.units_smul_comp, HomologicalComplex₂.ιTotal_map]

theorem quasiIsoAt_iff (n : ℕ) :
    QuasiIsoAt (HomologicalComplex₂.total.map (flipped f) (.up ℕ)) n ↔
      QuasiIsoAt (HomologicalComplex₂.total.map f (.up ℕ)) n := by
  rw [← quasiIsoAt_iff_comp_right (HomologicalComplex₂.total.map (flipped f) (.up ℕ))
    (C.totalFlipIso (.up ℕ)).hom n, natural,
    quasiIsoAt_iff_comp_left (B.totalFlipIso (.up ℕ)).hom]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.TotalFlip.TotalFlipNaturality
