import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TransitionDerivationLaws
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.DualProductComparison

/-! # Dual Chart Differences -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.DualChartDifferences

noncomputable section

/-! Two actual affine product trivializations with the same special-fiber
identification differ by a derivation. Triple comparisons form an additive
cocycle, and zero difference means the original trivializations agree. -/

open scoped TensorProduct

variable {k A S : Type*} [CommRing k] [CommRing A] [CommRing S]
    [Algebra k A] [Algebra (DualNumber k) S]

local instance smoothDualChartDifferences_commRing : CommRing (DualNumber k ⊗[k] A) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := A)

def dualProductChartTransition (f g : S ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A)) :
    (DualNumber k ⊗[k] A) ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A) := f.symm.trans g

theorem dualProductChartTransition_trans
    (f g h : S ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A)) :
    (dualProductChartTransition f g).trans (dualProductChartTransition g h) =
      dualProductChartTransition f h := by
  apply AlgEquiv.ext
  intro u
  change h (g.symm (g (f.symm u))) = h (f.symm u)
  rw [g.symm_apply_apply]

theorem dualProductChartTransition_reduction (q : S →+* A)
    (f g : S ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A))
    (hf : ∀ u, Dual.TensorReduction.dualTensorReduction k A (f u) = q u)
    (hg : ∀ u, Dual.TensorReduction.dualTensorReduction k A (g u) = q u) (u : DualNumber k ⊗[k] A) :
    Dual.TensorReduction.dualTensorReduction k A (dualProductChartTransition f g u) = Dual.TensorReduction.dualTensorReduction k A u :=
  (hg (f.symm u)).trans ((hf (f.symm u)).symm.trans
    (congrArg (Dual.TensorReduction.dualTensorReduction k A) (f.apply_symm_apply u)))

def dualProductChartDifference (q : S →+* A)
    (f g : S ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A))
    (hf : ∀ u, Dual.TensorReduction.dualTensorReduction k A (f u) = q u)
    (hg : ∀ u, Dual.TensorReduction.dualTensorReduction k A (g u) = q u) : Derivation k A A :=
  Dual.TransitionDerivationLaws.dualTensorTransitionDerivation (dualProductChartTransition f g)
    (dualProductChartTransition_reduction q f g hf hg)

theorem dualProductChartDifference_cocycle (q : S →+* A)
    (f g h : S ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A))
    (hf : ∀ u, Dual.TensorReduction.dualTensorReduction k A (f u) = q u)
    (hg : ∀ u, Dual.TensorReduction.dualTensorReduction k A (g u) = q u)
    (hh : ∀ u, Dual.TensorReduction.dualTensorReduction k A (h u) = q u) :
    dualProductChartDifference q f g hf hg + dualProductChartDifference q g h hg hh =
      dualProductChartDifference q f h hf hh := by
  unfold dualProductChartDifference
  rw [← Dual.TransitionDerivationLaws.dualTensorTransitionDerivation_trans]
  apply Derivation.ext
  intro a
  change (Dual.CoefficientLiftTensorMap.dualTensorTransitionCoordinates
    ((dualProductChartTransition f g).trans (dualProductChartTransition g h)) (TrivSqZeroExt.inl a)).snd =
      (Dual.CoefficientLiftTensorMap.dualTensorTransitionCoordinates (dualProductChartTransition f h) (TrivSqZeroExt.inl a)).snd
  rw [dualProductChartTransition_trans]

theorem dualProductChartDifference_eq_zero_iff (q : S →+* A)
    (f g : S ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A))
    (hf : ∀ u, Dual.TensorReduction.dualTensorReduction k A (f u) = q u)
    (hg : ∀ u, Dual.TensorReduction.dualTensorReduction k A (g u) = q u) :
    dualProductChartDifference q f g hf hg = 0 ↔ f = g := by
  constructor
  · intro hd
    let C := Dual.NumberCoefficients.dualTensorCoefficientEquiv k A
    let e := dualProductChartTransition f g
    let he := dualProductChartTransition_reduction q f g hf hg
    have hr := Dual.Derivation.dualDerivationAutomorphism_recover (Dual.CoefficientLiftTensorMap.dualTensorTransitionCoordinates e).toAlgHom
      (Dual.CoefficientLiftTensorMap.dualTensorTransitionCoordinates_reduction e he) (Dual.CoefficientLiftTensorMap.dualTensorTransitionCoordinates_eps e)
    change (Dual.Derivation.dualDerivationAutomorphism (dualProductChartDifference q f g hf hg)).toAlgHom =
      (Dual.CoefficientLiftTensorMap.dualTensorTransitionCoordinates e).toAlgHom at hr
    rw [hd, Dual.Derivation.dualDerivationAutomorphism_zero] at hr
    apply AlgEquiv.ext
    intro s
    apply C.injective
    have hs := AlgHom.congr_fun hr (C (f s))
    change C (f s) = C (g (f.symm (C.symm (C (f s))))) at hs
    rw [C.symm_apply_apply, f.symm_apply_apply] at hs
    exact hs
  · intro hfg
    subst g
    apply Derivation.ext
    intro a
    let C := Dual.NumberCoefficients.dualTensorCoefficientEquiv k A
    change (C (f (f.symm (C.symm (TrivSqZeroExt.inl a))))).snd = 0
    rw [f.apply_symm_apply, C.apply_symm_apply]
    rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.DualChartDifferences
