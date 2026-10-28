import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientLiftTensorMap

/-! # Transition Derivation Laws -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TransitionDerivationLaws

noncomputable section

/-! First-order coefficients turn actual dual-product composition into
addition. They also distinguish all base-preserving transition maps. -/

open scoped TensorProduct

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

theorem dualIdentityDerivation_comp
    (f g : DualNumber A →ₐ[k] DualNumber A)
    (hf : ∀ u, (f u).fst = u.fst) (hg : ∀ u, (g u).fst = u.fst)
    (hgeps : g DualNumber.eps = DualNumber.eps) :
    Dual.Derivation.dualIdentityDerivation (g.comp f) (fun u => (hg (f u)).trans (hf u)) =
      Dual.Derivation.dualIdentityDerivation f hf + Dual.Derivation.dualIdentityDerivation g hg := by
  apply Derivation.ext
  intro a
  have he := congrArg TrivSqZeroExt.snd
    (Dual.Derivation.dualReductionIdentity_normalForm g hg hgeps (f (TrivSqZeroExt.inl a)))
  change (g (f (TrivSqZeroExt.inl a))).snd =
    Dual.Derivation.dualIdentityDerivation g hg (f (TrivSqZeroExt.inl a)).fst + (f (TrivSqZeroExt.inl a)).snd at he
  rw [hf] at he
  change (g (f (TrivSqZeroExt.inl a))).snd =
    Dual.Derivation.dualIdentityDerivation g hg a + Dual.Derivation.dualIdentityDerivation f hf a at he
  change (g (f (TrivSqZeroExt.inl a))).snd =
    Dual.Derivation.dualIdentityDerivation f hf a + Dual.Derivation.dualIdentityDerivation g hg a
  exact he.trans (add_comm _ _)

theorem dualReductionIdentity_ext
    (f g : DualNumber A →ₐ[k] DualNumber A)
    (hf : ∀ u, (f u).fst = u.fst) (hg : ∀ u, (g u).fst = u.fst)
    (hfeps : f DualNumber.eps = DualNumber.eps) (hgeps : g DualNumber.eps = DualNumber.eps)
    (hd : Dual.Derivation.dualIdentityDerivation f hf = Dual.Derivation.dualIdentityDerivation g hg) : f = g := by
  apply AlgHom.ext
  intro u
  rw [Dual.Derivation.dualReductionIdentity_normalForm f hf hfeps, Dual.Derivation.dualReductionIdentity_normalForm g hg hgeps, hd]

local instance dualTransitionDerivationLaws_commRing : CommRing (DualNumber k ⊗[k] A) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := A)

theorem dualTensorTransitionCoordinates_trans
    (e t : (DualNumber k ⊗[k] A) ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A)) :
    CoefficientLiftTensorMap.dualTensorTransitionCoordinates (e.trans t) =
      (CoefficientLiftTensorMap.dualTensorTransitionCoordinates e).trans (CoefficientLiftTensorMap.dualTensorTransitionCoordinates t) := by
  apply AlgEquiv.ext
  intro u
  let C := NumberCoefficients.dualTensorCoefficientEquiv k A
  change C (t (e (C.symm u))) = C (t (C.symm (C (e (C.symm u)))))
  rw [C.symm_apply_apply]

def dualTensorTransitionDerivation
    (e : (DualNumber k ⊗[k] A) ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A))
    (he : ∀ u, TensorReduction.dualTensorReduction k A (e u) = TensorReduction.dualTensorReduction k A u) : Derivation k A A :=
  Dual.Derivation.dualIdentityDerivation (CoefficientLiftTensorMap.dualTensorTransitionCoordinates e).toAlgHom
    (CoefficientLiftTensorMap.dualTensorTransitionCoordinates_reduction e he)

theorem dualTensorTransitionDerivation_apply
    (e : (DualNumber k ⊗[k] A) ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A))
    (he : ∀ u, TensorReduction.dualTensorReduction k A (e u) = TensorReduction.dualTensorReduction k A u) (a : A) :
    dualTensorTransitionDerivation e he a =
      (CoefficientLiftTensorMap.dualTensorTransitionCoordinates e (TrivSqZeroExt.inl a)).snd := rfl

theorem dualTensorTransitionDerivation_trans
    (e t : (DualNumber k ⊗[k] A) ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A))
    (he : ∀ u, TensorReduction.dualTensorReduction k A (e u) = TensorReduction.dualTensorReduction k A u)
    (ht : ∀ u, TensorReduction.dualTensorReduction k A (t u) = TensorReduction.dualTensorReduction k A u) :
    dualTensorTransitionDerivation (e.trans t) (fun u => (ht (e u)).trans (he u)) =
      dualTensorTransitionDerivation e he + dualTensorTransitionDerivation t ht := by
  apply Derivation.ext
  intro a
  have hc := Derivation.congr_fun
    (dualIdentityDerivation_comp (CoefficientLiftTensorMap.dualTensorTransitionCoordinates e).toAlgHom
      (CoefficientLiftTensorMap.dualTensorTransitionCoordinates t).toAlgHom
      (CoefficientLiftTensorMap.dualTensorTransitionCoordinates_reduction e he)
      (CoefficientLiftTensorMap.dualTensorTransitionCoordinates_reduction t ht) (CoefficientLiftTensorMap.dualTensorTransitionCoordinates_eps t)) a
  have hm := congrArg (fun f : DualNumber A ≃ₐ[k] DualNumber A => (f (TrivSqZeroExt.inl a)).snd)
    (dualTensorTransitionCoordinates_trans e t)
  exact hm.trans hc

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TransitionDerivationLaws
