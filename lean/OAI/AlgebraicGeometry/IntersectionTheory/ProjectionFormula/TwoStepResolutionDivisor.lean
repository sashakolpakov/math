import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ComplexDeterminantEffective
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResolutionLocalCokernel
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResolutionBaseChangeEndpoints
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResolutionRankBalance

/-! # Two Step Resolution Divisor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TwoStepResolutionDivisor

noncomputable section

/-! A torsion module with a finite free resolution of length two has an
effective principal divisor with its actual height-one localized lengths. -/

set_option backward.isDefEq.respectTransparency false

open _root_.Module _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct Classical

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsLocalRing R] [IsIntegrallyClosed R]
  (M : ModuleCat.{u} R) [Module.Finite R M] (P : ProjectiveResolution M)

theorem exists_equation
    (hP : ∀ n, Module.Finite R (P.complex.X n) ∧ Module.Free R (P.complex.X n))
    (hd : IsZero (P.complex.X 3)) (r : R) (hr : r ≠ 0) (hM : ∀ x : M, r • x = 0) :
    ∃ a : R, a ≠ 0 ∧ ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      Ring.ord (Localization.AtPrime p) (algebraMap R (Localization.AtPrime p) a) =
        Module.length (Localization.AtPrime p) ((Localization.AtPrime p) ⊗[R] M) := by
  let : Module.Free R (P.complex.X 0) := (hP 0).2
  let : Module.Free R (P.complex.X 1) := (hP 1).2
  let : Module.Free R (P.complex.X 2) := (hP 2).2
  let : Module.Finite R (P.complex.X 0) := (hP 0).1
  let : Module.Finite R (P.complex.X 1) := (hP 1).1
  let : Module.Finite R (P.complex.X 2) := (hP 2).1
  let a := Module.finBasis R (P.complex.X 2)
  let c := Module.finBasis R (P.complex.X 0)
  have hdim := ResolutionRankBalance.rank_eq R M P hP hd r hr hM
  let b := (Module.finBasis R (P.complex.X 1)).reindex
    ((finCongr hdim).trans finSumFinEquiv.symm)
  let t := (ResolutionScalarContraction.lift R M P r hM).hom
  have hf : Function.Injective (P.complex.d 2 1).hom :=
    (ModuleCat.mono_iff_injective _).mp ((P.exact_succ 1).mono_g (hd.eq_of_src _ _))
  have ht : Function.Injective ((P.complex.d 1 0).hom.comp t) := by
    have he : (P.complex.d 1 0).hom.comp t = r • LinearMap.id :=
      ModuleCat.hom_ext_iff.mp (ResolutionScalarContraction.lift_comp R M P r hM)
    rw [he]
    exact smul_right_injective _ hr
  obtain ⟨v, hv, ho⟩ := ComplexDeterminantEffective.exists_equation R
    (P.complex.d 2 1).hom (P.complex.d 1 0).hom _ hf t ht a b c
    (fun p _ _ => ResolutionLocalCokernel.exact R M P (Localization.AtPrime p))
  refine ⟨v, hv, ?_⟩
  intro p hprime hp
  exact (ho p hp).trans (ResolutionLocalCokernel.length R M P (Localization.AtPrime p))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TwoStepResolutionDivisor
