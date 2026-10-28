import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Total
import OAI.AlgebraicGeometry.Comparison.Betti.Module.CechFunctor
import OAI.AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary
import OAI.AlgebraicTopology.DeRham.Comparison.CechTotalFunctor

/-! # Ordinary Cech -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.OrdinaryCech.IntrinsicOrdinary

noncomputable section

/-! The native categorical Čech total and the ordinary section-family
total are canonically isomorphic, including the interchange sign. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {X ι : Type} [TopologicalSpace X] (U : ι → Opens X)
  (K : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{0} ℂ) ℕ)

def nativeBicomplex := CechCoefficient.Total.bicomplex (FormalCoproduct.mk ι U).cech K

def ordinaryBicomplex : HomologicalComplex₂ (ModuleCat.{0} ℂ) (.up ℕ) (.up ℕ) :=
  ((AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor.cechComplexFunctor U).mapHomologicalComplex (.up ℕ)).obj K

def bicomplexIso : nativeBicomplex U K ≅ ordinaryBicomplex U K :=
  (NatIso.mapHomologicalComplex (AlgebraicGeometry.Comparison.Betti.Module.CechFunctor.moduleCechFunctorIso U) (.up ℕ)).app K

def totalIso : (nativeBicomplex U K).total (.up ℕ) ≅ AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalComplex U K :=
  HomologicalComplex₂.total.mapIso (bicomplexIso U K) (.up ℕ) ≪≫
    ((ordinaryBicomplex U K).totalFlipIso (.up ℕ)).symm

theorem inclusion_totalIso (p a n : ℕ) (hpa : p + a = n) :
    (nativeBicomplex U K).ιTotal (.up ℕ) p a n hpa ≫ (totalIso U K).hom.f n =
      (-1 : ℤ) ^ (p * a) •
        ((AlgebraicGeometry.Comparison.Betti.Module.CechCoordinates.moduleCechCoordinatesIso (K.X p) U a).hom ≫
          AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalInclusion U K a p n (by omega)) := by
  change (nativeBicomplex U K).ιTotal (.up ℕ) p a n hpa ≫
    ((HomologicalComplex₂.total.map (bicomplexIso U K).hom (.up ℕ)).f n ≫
      ((ordinaryBicomplex U K).totalFlipIso (.up ℕ)).inv.f n) = _
  rw [← Category.assoc, HomologicalComplex₂.ιTotal_map, Category.assoc,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_inv]
  change (AlgebraicGeometry.Comparison.Betti.Module.CechCoordinates.moduleCechCoordinatesIso (K.X p) U a).hom ≫
      (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) p a •
        AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalInclusion U K a p n (by omega)) = _
  rw [Linear.comp_units_smul]
  simp only [AlgebraicGeometry.SheafCohomology.Cech.TotalComplexUpNat.ComplexShape.σ_up_ℕ, Units.smul_def, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one]

theorem inclusion_zero_totalIso (p : ℕ) :
    (nativeBicomplex U K).ιTotal (.up ℕ) p 0 p (Nat.add_zero p) ≫ (totalIso U K).hom.f p =
      (AlgebraicGeometry.Comparison.Betti.Module.CechCoordinates.moduleCechCoordinatesIso (K.X p) U 0).hom ≫
        AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalInclusion U K 0 p p (Nat.zero_add p) := by
  rw [inclusion_totalIso]
  simp only [Nat.mul_zero, pow_zero, one_smul]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.OrdinaryCech.IntrinsicOrdinary
