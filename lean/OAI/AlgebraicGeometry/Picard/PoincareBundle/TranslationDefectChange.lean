import OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationRatio
import OAI.AlgebraicGeometry.Picard.PoincareBundle.TransportDefectComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.DefectCocycle

/-! # Translation Defect Change -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TranslationDefectChange

noncomputable section

/-! Changing a subgroup translation alters the regular defect by its comparison coboundary. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationFibers
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberIsomorphismRatios OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationDefect OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.DefectCocycle

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H A : Over (Spec (.of k))} [GrpObj H] [IsCommMonObj H] [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]
  (i : H ⟶ A) [IsMonHom i] (L : Line.Bundles.LineBundle A.left)
  (t s : Line.Fibers.fiber L (snd H A) ≅ Line.Fibers.fiber L (NormalizedKernelTranslation.action i))

theorem compare_at_points {T : Over (Spec (.of k))} (x y z : T ⟶ A) (a b c : T ⟶ H)
    (hx : (a ≫ i) * x = y) (hy : (b ≫ i) * y = z) (hz : (c ≫ i) * x = z) (hc : a * b = c) :
    Subgroup.DefectParameters.value i L t a b * Subgroup.TranslationRatio.value i L t s c =
      Subgroup.TranslationRatio.value i L t s a * Subgroup.TranslationRatio.value i L t s b *
        Subgroup.DefectParameters.value i L s a b := by
  have h := TransportDefectComparison.compare (FiberIsomorphismRatios.fiberLine L x) (FiberIsomorphismRatios.fiberLine L y)
    (Subgroup.TranslationFibers.transportIso i L t x y a hx) (Subgroup.TranslationFibers.transportIso i L s x y a hx)
    (Subgroup.TranslationFibers.transportIso i L t y z b hy) (Subgroup.TranslationFibers.transportIso i L s y z b hy)
    (Subgroup.TranslationFibers.transportIso i L t x z c hz) (Subgroup.TranslationFibers.transportIso i L s x z c hz)
  have ht := Subgroup.DefectCocycle.defect_eq_parameter i L t x y z a b c hx hy hz hc
  have hs := Subgroup.DefectCocycle.defect_eq_parameter i L s x y z a b c hx hy hz hc
  have ha := Subgroup.TranslationRatio.point_ratio i L t s x y a hx
  have hb := Subgroup.TranslationRatio.point_ratio i L t s y z b hy
  have hd := Subgroup.TranslationRatio.point_ratio i L t s x z c hz
  exact (congrArg₂ (· * ·) ht hd).symm.trans
    (h.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) ha hb) hs))

/-- The two genuine regular defects differ by the subgroup comparison units. -/
theorem coboundary {T : Over (Spec (.of k))} (a b : T ⟶ H) :
    Subgroup.DefectParameters.value i L t a b * Subgroup.TranslationRatio.value i L t s (a * b) =
      Subgroup.TranslationRatio.value i L t s a * Subgroup.TranslationRatio.value i L t s b *
        Subgroup.DefectParameters.value i L s a b :=
  compare_at_points i L t s 1 ((a ≫ i) * 1) (((a * b) ≫ i) * 1) a b (a * b)
    rfl (Subgroup.ProductDefect.translate_mul i a b 1) rfl rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TranslationDefectChange
