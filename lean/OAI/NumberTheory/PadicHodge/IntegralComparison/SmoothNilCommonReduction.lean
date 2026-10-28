import OAI.NumberTheory.PadicHodge.IntegralComparison.PointedSmoothNilLift
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.NilCommonReduction

/-! # Smooth Nil Common Reduction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothNilCommonReduction.Pointed

noncomputable section

/-! Smooth affine models with the same special fiber and compatible
sections admit an actual isomorphism preserving both identifications. -/

universe u v w z
variable {R : Type u} [CommRing R]
  {A : Type v} [CommRing A] [Algebra R A]
  {B : Type w} [CommRing B] [Algebra R B]
  {C : Type z} [CommRing C] [Algebra R C]
  (I : Ideal R) (hI : IsNilpotent I)
  [Algebra.FormallySmooth R A] [Module.Flat R B]
  (πA : A →ₐ[R] C) (hA : Function.Surjective πA)
  (hAker : RingHom.ker πA.toRingHom = I.map (algebraMap R A))
  (πB : B →ₐ[R] C) (hB : Function.Surjective πB)
  (hBker : RingHom.ker πB.toRingHom = I.map (algebraMap R B))
  (εA : A →ₐ[R] R) (εB : B →ₐ[R] R) (εC : C →ₐ[R] R ⧸ I)
  (hεA : εC.comp πA = (Ideal.Quotient.mkₐ R I).comp εA)
  (hεB : εC.comp πB = (Ideal.Quotient.mkₐ R I).comp εB)

include hI hA hAker hB hBker hεA hεB in
theorem exists_equiv : ∃ e : A ≃ₐ[R] B,
    πB.comp e.toAlgHom = πA ∧ εB.comp e.toAlgHom = εA := by
  have hnil : IsNilpotent (RingHom.ker πB.toRingHom) := by
    rw [hBker]
    exact AlgebraicGeometry.Resolution.Blowups.Etale.FiniteNeighborhood.Construction.ideal_map_isNilpotent I hI
  have hbase : I ≤ RingHom.ker (algebraMap R C) := by
    intro r hr
    have hb : algebraMap R B r ∈ RingHom.ker πB.toRingHom := by
      rw [hBker]
      exact Ideal.mem_map_of_mem (algebraMap R B) hr
    exact (πB.commutes r).symm.trans hb
  obtain ⟨f, hf, hpoint⟩ := PointedSmoothNilLift.exists_lift
    I πA πB εA εB εC hεA hεB hB hnil hbase
  let eA := Smooth.NilCommonReduction.quotientEquiv I πA hA hAker
  let eB := Smooth.NilCommonReduction.quotientEquiv I πB hB hBker
  have hred : (Ideal.Quotient.mkₐ R (I.map (algebraMap R B))).comp f =
      (eA.trans eB.symm).toAlgHom.comp (Ideal.Quotient.mkₐ R (I.map (algebraMap R A))) := by
    apply AlgHom.ext
    intro a
    apply eB.injective
    change eB (Ideal.Quotient.mk _ (f a)) = eB (eB.symm (eA (Ideal.Quotient.mk _ a)))
    rw [eB.apply_symm_apply]
    exact AlgHom.congr_fun hf a
  exact ⟨AlgEquiv.ofBijective f
    (Smooth.NilReductionEquiv.bijective_of_reduction I hI (eA.trans eB.symm) f hred), hf, hpoint⟩

def equiv : A ≃ₐ[R] B :=
  (exists_equiv I hI πA hA hAker πB hB hBker εA εB εC hεA hεB).choose

theorem reduction_equiv : πB.comp
    (equiv I hI πA hA hAker πB hB hBker εA εB εC hεA hεB).toAlgHom = πA :=
  (exists_equiv I hI πA hA hAker πB hB hBker εA εB εC hεA hεB).choose_spec.1

theorem section_equiv : εB.comp
    (equiv I hI πA hA hAker πB hB hBker εA εB εC hεA hεB).toAlgHom = εA :=
  (exists_equiv I hI πA hA hAker πB hB hBker εA εB εC hεA hεB).choose_spec.2

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothNilCommonReduction.Pointed
