import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechZero
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechFunctor
import OAI.AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary

/-! # Cech Forget -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForget

noncomputable section

/-! Forgetting support is the actual zeroth Čech-column projection,
followed by the empty-intersection identification. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {D : Type v} [Category D] [Preadditive D] [HasProducts.{u} D]
  (K : CochainComplex (Cᵒᵖ ⥤ D) ℕ) [(CechFunctor.bicomplex U K).HasTotal (.up ℕ)]

abbrev ambientComplex :=
  (((CategoryTheory.evaluation Cᵒᵖ D).obj (op (⊤_ C))).mapHomologicalComplex (.up ℕ)).obj K

def forgetSupport : (CechFunctor.bicomplex U K).total (.up ℕ) ⟶ ambientComplex K where
  f n := (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (CechFunctor.bicomplex U K)) n 0 n ≫ (CechZero.zeroIso U (K.X n)).hom
  comm' n m h := by
    obtain rfl : m = n + 1 := h.symm
    change (_ ≫ _) ≫ (K.d n (n + 1)).app (op (⊤_ C)) = _ ≫ (_ ≫ _)
    have hn := CechZero.zeroIso_naturality U (K.X n) (K.d n (n + 1))
    change CechFunctor.objectMap U (K.d n (n + 1)) 0 ≫ (CechZero.zeroIso U (K.X (n + 1))).hom =
      (CechZero.zeroIso U (K.X n)).hom ≫ (K.d n (n + 1)).app (op (⊤_ C)) at hn
    calc
      _ = (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (CechFunctor.bicomplex U K)) n 0 n ≫
          (CechFunctor.objectMap U (K.d n (n + 1)) 0 ≫ (CechZero.zeroIso U (K.X (n + 1))).hom) :=
        (Category.assoc _ _ _).trans (congrArg ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (CechFunctor.bicomplex U K)) n 0 n ≫ ·) hn.symm)
      _ = ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (CechFunctor.bicomplex U K)) n 0 n ≫
          ((CechFunctor.bicomplex U K).d n (n + 1)).f 0) ≫ (CechZero.zeroIso U (K.X (n + 1))).hom :=
        (Category.assoc _ _ _).symm
      _ = _ := (congrArg (· ≫ (CechZero.zeroIso U (K.X (n + 1))).hom)
        (AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary.Projective.total_d_π_zero_right (CechFunctor.bicomplex U K) n).symm).trans (Category.assoc _ _ _)

theorem forgetSupport_f (n : ℕ) : (forgetSupport U K).f n =
    (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (CechFunctor.bicomplex U K)) n 0 n ≫ (CechZero.zeroIso U (K.X n)).hom := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForget
