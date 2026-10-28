import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationField
import Mathlib.RingTheory.Etale.Pi

/-! # Evaluation Field -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.EvaluationField.Lifts

noncomputable section

/-! One finite extension simultaneously evaluates any finite family of
finite etale algebras. This includes all three neighbor parameters and
the generic torsion algebra in the same construction. -/

open scoped TensorProduct

universe u

theorem finiteSplit_of_surjective (k A B : Type u) [Field k]
    [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [Algebra.IsFiniteSplit k A] [Module.Finite k B] [Algebra.Etale k B]
    (f : A →ₐ[k] B) (hf : Function.Surjective f) : Algebra.IsFiniteSplit k B := by
  have : IsArtinianRing B := IsArtinianRing.of_finite k B
  have : IsReduced B := Algebra.FormallyUnramified.isReduced_of_field k B
  have hbij (m : MaximalSpectrum B) : Function.Bijective (algebraMap k (B ⧸ m.asIdeal)) := by
    let g : A →ₐ[k] B ⧸ m.asIdeal := (Ideal.Quotient.mkₐ k m.asIdeal).comp f
    have hg : Function.Surjective g := (Ideal.Quotient.mk_surjective).comp hf
    let p := RingHom.ker g
    have : p.IsPrime := RingHom.ker_isPrime g
    let e : (A ⧸ p) ≃ₐ[k] B ⧸ m.asIdeal := Ideal.quotientKerAlgEquivOfSurjective hg
    have ha := Algebra.IsFiniteSplit.bijective_algebraMap_quotient k p
    refine ⟨(algebraMap k (B ⧸ m.asIdeal)).injective, ?_⟩
    intro b
    obtain ⟨c, hc⟩ := ha.surjective (e.symm b)
    exact ⟨c, (e.commutes c).symm.trans ((congrArg e hc).trans (e.apply_symm_apply b))⟩
  let e : B ≃ₐ[k] (MaximalSpectrum B → k) :=
    ((IsArtinianRing.equivPi B).restrictScalars k).trans
      (AlgEquiv.piCongrRight fun m ↦ (AlgEquiv.ofBijective (Algebra.ofId k (B ⧸ m.asIdeal))
        (hbij m)).symm)
  exact Algebra.IsFiniteSplit.of_algEquiv e.symm

theorem exists_joint_finite_evaluation_field (K : Type u) [Field K]
    {I : Type u} [Fintype I] (C : I → Type u)
    [∀ i, CommRing (C i)] [∀ i, Algebra K (C i)]
    [∀ i, Module.Finite K (C i)] [∀ i, Algebra.Etale K (C i)] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L),
      ∀ i, Algebra.IsFiniteSplit L (L ⊗[K] C i) := by
  classical
  obtain ⟨L, _, _, _, h⟩ := EvaluationField.Lifts.exists_finite_evaluation_field K (∀ i, C i)
  have : Algebra.IsFiniteSplit L (∀ i, L ⊗[K] C i) :=
    Algebra.IsFiniteSplit.of_algEquiv (Algebra.TensorProduct.piRight K L L C)
  refine ⟨L, inferInstance, inferInstance, inferInstance, ?_⟩
  intro i
  exact finiteSplit_of_surjective L (∀ j, L ⊗[K] C j) (L ⊗[K] C i)
    (Pi.evalAlgHom L (fun j ↦ L ⊗[K] C j) i) (Function.surjective_eval _)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.EvaluationField.Lifts
