import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubmersivePolynomialSplit

/-! # Submersive Split Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubmersiveSplitEvaluation

noncomputable section

/-! Evaluation of split polynomials agrees with the original assignment of all variables. -/

universe u v w t

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable {ι : Type w} {σ : Type t} (m : σ → ι) (hm : Function.Injective m) (v : ι → S)

def submersiveSplitEvaluation : MvPolynomial σ (MvPolynomial (SubmersivePolynomialSplit.UnselectedVariables m) R) →+* S :=
  MvPolynomial.eval₂Hom (MvPolynomial.aeval (fun i : SubmersivePolynomialSplit.UnselectedVariables m => v i.val)).toRingHom
    (fun j => v (m j))

theorem submersiveSplitEvaluation_comp :
    (submersiveSplitEvaluation R S m v).comp (SubmersivePolynomialSplit.submersivePolynomialSplit R m hm).toRingHom =
      (MvPolynomial.aeval v).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [submersiveSplitEvaluation, SubmersivePolynomialSplit.submersivePolynomialSplit]
  · intro i
    change submersiveSplitEvaluation R S m v (SubmersivePolynomialSplit.submersivePolynomialSplit R m hm (MvPolynomial.X i)) =
      MvPolynomial.aeval v (MvPolynomial.X i)
    obtain ⟨j, rfl⟩ := (SubmersivePolynomialSplit.injectionSumComplementEquiv m hm).surjective i
    cases j with
    | inl j => simp [submersiveSplitEvaluation]
    | inr i => simp [submersiveSplitEvaluation]

theorem submersiveSplitEvaluation_apply (p : MvPolynomial ι R) :
    submersiveSplitEvaluation R S m v (SubmersivePolynomialSplit.submersivePolynomialSplit R m hm p) = MvPolynomial.aeval v p :=
  RingHom.congr_fun (submersiveSplitEvaluation_comp R S m hm v) p

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubmersiveSplitEvaluation
