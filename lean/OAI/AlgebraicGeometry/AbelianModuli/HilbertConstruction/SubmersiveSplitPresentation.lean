import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubmersiveSplitGenerators
import Mathlib.RingTheory.Extension.Presentation.Basic

/-! # Submersive Split Presentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubmersiveSplitPresentation

noncomputable section

/-! Transporting the defining relations to the polynomial algebra in the selected variables. -/

universe u v w t

theorem ringEquiv_map_kernel {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (e : A ≃+* B) (f : A →+* C) (g : B →+* C) (h : g.comp e.toRingHom = f) :
    Ideal.map e.toRingHom (RingHom.ker f) = RingHom.ker g := by
  rw [← h, ← RingHom.comap_ker]
  exact Ideal.map_comap_of_surjective e.toRingHom e.surjective (RingHom.ker g)

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable {ι : Type w} {σ : Type t} (m : σ → ι) (hm : Function.Injective m)

theorem submersiveSplitGenerators_kernel (P : Algebra.Generators R S ι) :
    letI := SubmersiveSplitGenerators.submersiveFreeVariableAlgebra R S m P.val
    Ideal.map (SubmersivePolynomialSplit.submersivePolynomialSplit R m hm).toRingHom P.ker =
      (SubmersiveSplitGenerators.submersiveSplitGenerators R S m hm P).ker := by
  let := SubmersiveSplitGenerators.submersiveFreeVariableAlgebra R S m P.val
  rw [P.ker_eq_ker_aeval_val, Algebra.Generators.ker_eq_ker_aeval_val]
  exact ringEquiv_map_kernel (SubmersivePolynomialSplit.submersivePolynomialSplit R m hm).toRingEquiv
    (MvPolynomial.aeval P.val).toRingHom (SubmersiveSplitEvaluation.submersiveSplitEvaluation R S m P.val)
    (SubmersiveSplitEvaluation.submersiveSplitEvaluation_comp R S m hm P.val)

def submersiveSplitPresentation (P : Algebra.Presentation R S ι σ) :
    letI := SubmersiveSplitGenerators.submersiveFreeVariableAlgebra R S m P.val
    Algebra.Presentation (MvPolynomial (SubmersivePolynomialSplit.UnselectedVariables m) R) S σ σ := by
  letI := SubmersiveSplitGenerators.submersiveFreeVariableAlgebra R S m P.val
  refine
    { toGenerators := SubmersiveSplitGenerators.submersiveSplitGenerators R S m hm P.toGenerators
      relation := fun j => SubmersivePolynomialSplit.submersivePolynomialSplit R m hm (P.relation j)
      span_range_relation_eq_ker := ?_ }
  rw [← submersiveSplitGenerators_kernel R S m hm P.toGenerators,
    ← P.span_range_relation_eq_ker, Ideal.map_span, ← Set.range_comp]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubmersiveSplitPresentation
