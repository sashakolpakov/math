import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.KernelApproximation
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TorsionPresentationRank
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ComplexDeterminantCorrection
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TwoStepResolutionDivisor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.BoundedResolution

/-! # Resolution Divisor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ResolutionDivisor

noncomputable section

/-! A finite torsion module of finite projective dimension over a normal
noetherian local domain has an effective principal divisor with its exact
height-one localized lengths. The proof inducts on projective dimension. -/

set_option backward.isDefEq.respectTransparency false

open _root_.Module _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct Classical

universe u

theorem exists_equation (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsLocalRing R] [IsIntegrallyClosed R]
    (M : ModuleCat.{u} R) [Module.Finite R M] (d : ℕ) [HasProjectiveDimensionLE M d]
    (r : R) (hr : r ≠ 0) (hM : ∀ x : M, r • x = 0) :
    ∃ a : R, a ≠ 0 ∧ ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      Ring.ord (Localization.AtPrime p) (algebraMap R (Localization.AtPrime p) a) =
        Module.length (Localization.AtPrime p) ((Localization.AtPrime p) ⊗[R] M) := by
  induction d using Nat.strong_induction_on generalizing M r with
  | h d ih =>
    by_cases hd : d ≤ 2
    · let : HasProjectiveDimensionLE M 2 := hasProjectiveDimensionLT_of_ge M (d + 1) 3 (by omega)
      obtain ⟨P, hP, hbound⟩ := BoundedResolution.exists_finite_free_bounded_resolution R M 2
      exact TwoStepResolutionDivisor.exists_equation R M P hP (hbound 3 (by omega)) r hr hM
    · obtain ⟨k, rfl⟩ : ∃ k, d = k + 3 := ⟨d - 3, by omega⟩
      obtain ⟨P, hP, _⟩ := BoundedResolution.exists_finite_free_bounded_resolution R M (k + 3)
      let B := P.complex.X 1
      let C := P.complex.X 0
      let : Module.Finite R B := (hP 1).1
      let : Module.Free R B := (hP 1).2
      let : Module.Finite R C := (hP 0).1
      let : Module.Free R C := (hP 0).2
      let g : B →ₗ[R] C := (P.complex.d 1 0).hom
      let π : C →ₗ[R] M := (P.π.f 0).hom
      have he : Function.Exact g π :=
        (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp P.exact₀
      have hπ : Function.Surjective π := (ModuleCat.epi_iff_surjective _).mp inferInstance
      let : Module.Finite R g.ker := Module.Finite.of_injective g.ker.subtype g.ker.subtype_injective
      obtain ⟨N, hNfree, hNfin, hNrank, s, hs, hH⟩ := Generic.FreeSubmodule.exists_submodule R g.ker
      let : Module.Free R N := hNfree
      let : Module.Finite R N := hNfin
      let H := ModuleCat.of R (g.ker ⧸ N)
      let : HasProjectiveDimensionLE H (k + 1) :=
        KernelApproximation.residual_dimension R B C g N M π he hπ k
      obtain ⟨v, hv, ho⟩ := ih (k + 1) (by omega) H s hs hH
      let f := KernelApproximation.map R B C g N
      have hfg : g.comp f = 0 := KernelApproximation.comp_zero R B C g N
      have hf : Function.Injective f := KernelApproximation.map_injective R B C g N
      let t := (ResolutionScalarContraction.lift R M P r hM).hom
      have ht : Function.Injective (g.comp t) := by
        have ht' : g.comp t = r • LinearMap.id :=
          ModuleCat.hom_ext_iff.mp (ResolutionScalarContraction.lift_comp R M P r hM)
        rw [ht']
        exact smul_right_injective _ hr
      have htor : Module.IsTorsion R M := fun x =>
        ⟨⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr⟩, hM x⟩
      have hdim : Module.finrank R B = Module.finrank R N + Module.finrank R C := by
        rw [hNrank]
        exact TorsionPresentationRank.rank_eq R B C M g π he hπ htor
      let a := Module.finBasis R N
      let c := Module.finBasis R C
      let b := (Module.finBasis R B).reindex ((finCongr hdim).trans finSumFinEquiv.symm)
      obtain ⟨z, hz, hzo⟩ := ComplexDeterminantCorrection.exists_equation R f g hfg hf t ht a b c v hv
        (fun p _ hp => (KernelApproximation.baseChange_length R B C g N (Localization.AtPrime p)).trans
          (ho p hp).symm)
      exact ⟨z, hz, fun p _ hp => (hzo p hp).trans
        (ResolutionLocalCokernel.length R M P (Localization.AtPrime p))⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ResolutionDivisor
