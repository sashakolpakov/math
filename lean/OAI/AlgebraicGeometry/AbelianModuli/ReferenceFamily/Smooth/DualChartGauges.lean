import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.DualChartDifferences
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorDerivationGauges

/-! # Dual Chart Gauges -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.DualChartGauges

noncomputable section

/-! Actual derivation gauges change affine product-trivialization
differences by the precise additive coboundary. A coboundary therefore
gives literally equal adjusted trivializations. -/

open scoped TensorProduct

variable {k A S : Type*} [CommRing k] [CommRing A] [CommRing S]
    [Algebra k A] [Algebra (DualNumber k) S]

local instance smoothDualChartGauges_commRing : CommRing (DualNumber k ⊗[k] A) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := A)

def gaugeDualProductChart (f : S ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A)) (d : Derivation k A A) :
    S ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A) := f.trans (Dual.TensorDerivationGauges.dualTensorDerivationGauge d)

theorem gaugeDualProductChart_reduction (q : S →+* A)
    (f : S ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A))
    (hf : ∀ u, Dual.TensorReduction.dualTensorReduction k A (f u) = q u) (d : Derivation k A A) (u : S) :
    Dual.TensorReduction.dualTensorReduction k A (gaugeDualProductChart f d u) = q u :=
  (Dual.TensorDerivationGauges.dualTensorDerivationGauge_reduction d (f u)).trans (hf u)

theorem dualProductChartDifference_gauge (q : S →+* A)
    (f : S ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A))
    (hf : ∀ u, Dual.TensorReduction.dualTensorReduction k A (f u) = q u) (d : Derivation k A A) :
    DualChartDifferences.dualProductChartDifference q f (gaugeDualProductChart f d) hf
      (gaugeDualProductChart_reduction q f hf d) = d := by
  have he : DualChartDifferences.dualProductChartTransition f (gaugeDualProductChart f d) = Dual.TensorDerivationGauges.dualTensorDerivationGauge d := by
    apply AlgEquiv.ext
    intro u
    change Dual.TensorDerivationGauges.dualTensorDerivationGauge d (f (f.symm u)) = Dual.TensorDerivationGauges.dualTensorDerivationGauge d u
    rw [f.apply_symm_apply]
  apply Derivation.ext
  intro a
  change (Dual.CoefficientLiftTensorMap.dualTensorTransitionCoordinates (DualChartDifferences.dualProductChartTransition f (gaugeDualProductChart f d))
    (TrivSqZeroExt.inl a)).snd = d a
  rw [he, Dual.TensorDerivationGauges.dualTensorDerivationGauge_coordinates]
  change d a + 0 = d a
  exact add_zero _

theorem dualProductChartDifference_gauged (q : S →+* A)
    (f g : S ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A))
    (hf : ∀ u, Dual.TensorReduction.dualTensorReduction k A (f u) = q u)
    (hg : ∀ u, Dual.TensorReduction.dualTensorReduction k A (g u) = q u) (d e : Derivation k A A) :
    DualChartDifferences.dualProductChartDifference q (gaugeDualProductChart f d) (gaugeDualProductChart g e)
      (gaugeDualProductChart_reduction q f hf d) (gaugeDualProductChart_reduction q g hg e) =
        DualChartDifferences.dualProductChartDifference q f g hf hg + e - d := by
  have h₁ := DualChartDifferences.dualProductChartDifference_cocycle q f (gaugeDualProductChart f d) (gaugeDualProductChart g e)
    hf (gaugeDualProductChart_reduction q f hf d) (gaugeDualProductChart_reduction q g hg e)
  have h₂ := DualChartDifferences.dualProductChartDifference_cocycle q f g (gaugeDualProductChart g e)
    hf hg (gaugeDualProductChart_reduction q g hg e)
  rw [dualProductChartDifference_gauge] at h₁ h₂
  apply eq_sub_iff_add_eq.mpr
  exact (add_comm _ _).trans (h₁.trans h₂.symm)

theorem gaugeDualProductChart_eq_of_coboundary (q : S →+* A)
    (f g : S ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A))
    (hf : ∀ u, Dual.TensorReduction.dualTensorReduction k A (f u) = q u)
    (hg : ∀ u, Dual.TensorReduction.dualTensorReduction k A (g u) = q u) (d e : Derivation k A A)
    (hde : DualChartDifferences.dualProductChartDifference q f g hf hg = d - e) :
    gaugeDualProductChart f d = gaugeDualProductChart g e := by
  apply (DualChartDifferences.dualProductChartDifference_eq_zero_iff q (gaugeDualProductChart f d) (gaugeDualProductChart g e)
    (gaugeDualProductChart_reduction q f hf d) (gaugeDualProductChart_reduction q g hg e)).mp
  rw [dualProductChartDifference_gauged q f g hf hg d e, hde]
  abel

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.DualChartGauges
