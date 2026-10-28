import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NilpotentLinearMapLifting
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.FiniteNeighborhood
import Mathlib.RingTheory.Smooth.Basic

/-! # Nil Reduction Equiv -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.NilReductionEquiv

noncomputable section

/-! An affine smooth lift across a nilpotent base ideal is determined,
up to an actual base-algebra isomorphism, by its reduction. This uses
smooth lifting and the genuine flat nilpotent isomorphism criterion. -/
open TensorProduct
universe u v w
variable {R : Type u} [CommRing R]
  {A : Type v} [CommRing A] [Algebra R A]
  {B : Type w} [CommRing B] [Algebra R B]
  (I : Ideal R) (hI : IsNilpotent I)

include hI in
theorem bijective_of_reduction [Module.Flat R B]
    (e : (A ⧸ I.map (algebraMap R A)) ≃ₐ[R] (B ⧸ I.map (algebraMap R B)))
    (f : A →ₐ[R] B)
    (hf : (Ideal.Quotient.mkₐ R (I.map (algebraMap R B))).comp f =
      e.toAlgHom.comp (Ideal.Quotient.mkₐ R (I.map (algebraMap R A)))) :
    Function.Bijective f := by
  apply AlgebraicGeometry.HilbertScheme.Presentations.NilpotentLinearMapLifting.nilpotent_bijective_of_reduction I hI f.toLinearMap
  let eA := Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I
  let eB := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I
  have hcomp : f.toLinearMap.lTensor (R ⧸ I) ∘ eA = eB ∘ e := by
    funext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha := AlgHom.congr_fun hf a
    change Ideal.Quotient.mk _ (f a) = e (Ideal.Quotient.mk _ a) at ha
    change f.toLinearMap.lTensor (R ⧸ I) (1 ⊗ₜ[R] a) =
      eB (e (Ideal.Quotient.mk _ a))
    rw [← ha]
    rfl
  exact (Function.Bijective.of_comp_iff _ eA.bijective).mp
    (hcomp.symm ▸ eB.bijective.comp e.bijective)

include hI in
theorem exists_equiv [Algebra.FormallySmooth R A] [Module.Flat R B]
    (e : (A ⧸ I.map (algebraMap R A)) ≃ₐ[R] (B ⧸ I.map (algebraMap R B))) :
    ∃ f : A ≃ₐ[R] B,
      (Ideal.Quotient.mkₐ R (I.map (algebraMap R B))).comp f.toAlgHom =
        e.toAlgHom.comp (Ideal.Quotient.mkₐ R (I.map (algebraMap R A))) := by
  obtain ⟨f, hf⟩ := Algebra.FormallySmooth.exists_lift (I.map (algebraMap R B))
    (AlgebraicGeometry.Resolution.Blowups.Etale.FiniteNeighborhood.Construction.ideal_map_isNilpotent I hI)
    (e.toAlgHom.comp (Ideal.Quotient.mkₐ R (I.map (algebraMap R A))))
  exact ⟨AlgEquiv.ofBijective f (bijective_of_reduction I hI e f hf), hf⟩

def equiv [Algebra.FormallySmooth R A] [Module.Flat R B]
    (e : (A ⧸ I.map (algebraMap R A)) ≃ₐ[R] (B ⧸ I.map (algebraMap R B))) : A ≃ₐ[R] B :=
  (exists_equiv I hI e).choose

theorem reduction_equiv [Algebra.FormallySmooth R A] [Module.Flat R B]
    (e : (A ⧸ I.map (algebraMap R A)) ≃ₐ[R] (B ⧸ I.map (algebraMap R B))) :
    (Ideal.Quotient.mkₐ R (I.map (algebraMap R B))).comp (equiv I hI e).toAlgHom =
      e.toAlgHom.comp (Ideal.Quotient.mkₐ R (I.map (algebraMap R A))) :=
  (exists_equiv I hI e).choose_spec

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.NilReductionEquiv
