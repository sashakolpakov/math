import OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.HypersurfaceCenters
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Center Quotient -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.CenterQuotient.Construction

noncomputable section

/-! The lifted center has exactly the hypersurface center as its scheme structure. -/

variable {H R : Type*} [CommRing H] [CommRing R] [Algebra H R]

/-- Quotienting by the lifted center gives the actual quotient by the
hypersurface center, with every original section mapped as prescribed. -/
theorem exists_retracted_center_quotient_equiv (z : R)
    (e : (R ⧸ Ideal.span {z}) ≃ₐ[H] H) (K : Ideal H) :
    ∃ E : (R ⧸ (K.map (algebraMap H R) ⊔ Ideal.span {z})) ≃ₐ[H] (H ⧸ K),
      ∀ x : R, E (Ideal.Quotient.mk _ x) =
        Ideal.Quotient.mk K (e (Ideal.Quotient.mk (Ideal.span {z}) x)) := by
  let I := K.map (algebraMap H R) ⊔ Ideal.span {z}
  let F : R →ₐ[H] H ⧸ K := (Ideal.Quotient.mkₐ H K).comp
    (e.toAlgHom.comp (Ideal.Quotient.mkₐ H (Ideal.span {z})))
  have hF : Function.Surjective F :=
    Ideal.Quotient.mk_surjective.comp (e.surjective.comp Ideal.Quotient.mk_surjective)
  have hker : RingHom.ker F.toRingHom = I := by
    ext x
    change Ideal.Quotient.mk K (e (Ideal.Quotient.mk (Ideal.span {z}) x)) = 0 ↔ x ∈ I
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change e (Ideal.Quotient.mk (Ideal.span {z}) x) ∈ K ↔
      x ∈ K.map (algebraMap H R) ⊔ Ideal.span {z}
    rw [HypersurfaceCenters.Construction.retracted_hypersurface_center_comap z e K]
    rfl
  let E : (R ⧸ I) ≃ₐ[H] H ⧸ K := (Ideal.quotientEquivAlgOfEq H hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hF)
  refine ⟨E, ?_⟩
  intro x
  change Ideal.quotientKerAlgEquivOfSurjective hF
    (Ideal.quotientEquivAlgOfEq H hker.symm (Ideal.Quotient.mk I x)) = _
  rw [Ideal.quotientEquivAlgOfEq_mk]
  exact Ideal.quotientKerAlgEquivOfSurjective_mk (f := F) hF x

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.CenterQuotient.Construction
