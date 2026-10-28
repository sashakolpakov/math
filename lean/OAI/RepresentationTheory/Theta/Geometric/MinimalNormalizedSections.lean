import OAI.RepresentationTheory.Theta.Geometric.Normalized.KernelBaseChange
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.MinimalResidueSections

/-! # Minimal Normalized Sections -/

namespace OAI.RepresentationTheory.Theta.Geometric.MinimalNormalizedSections

noncomputable section

/-! Normalization of actual first cycles is preserved by the minimal
finite-complex comparison, on every scalar extension. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R]

theorem scalarFunctionalBaseChange_comp
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (T : Type u) [CommRing T] [Algebra R T] (v : N →ₗ[R] R) (f : M →ₗ[R] N)
    (m : T ⊗[R] M) :
    Normalized.KernelBaseChange.scalarFunctionalBaseChange T (v.comp f) m =
      Normalized.KernelBaseChange.scalarFunctionalBaseChange T v (f.baseChange T m) := by
  unfold Normalized.KernelBaseChange.scalarFunctionalBaseChange
  rw [LinearMap.baseChange_comp]
  rfl

variable [IsLocalRing R] {S : ShortComplex (ModuleCat.{u} R)}
    (P : AlgebraicGeometry.Quotients.FiniteDescent.LocalMinimalShort.Construction.LocalSectionLifting.LocalMinimalShortComplex S)

def minimalSectionFunctional (v : S.X₁ →ₗ[R] R) : P.complex.X₁ →ₗ[R] R :=
  v.comp P.equivalence.inv.τ₁.hom

theorem normalized_minimal_cycles_iff
    (T : Type u) [CommRing T] [Algebra R T] (v : S.X₁ →ₗ[R] R) :
    (∃ m : T ⊗[R] S.X₁, S.f.hom.baseChange T m = 0 ∧
      Normalized.KernelBaseChange.scalarFunctionalBaseChange T v m = 1) ↔
    (∃ m : T ⊗[R] P.complex.X₁, P.complex.f.hom.baseChange T m = 0 ∧
      Normalized.KernelBaseChange.scalarFunctionalBaseChange T (minimalSectionFunctional P v) m = 1) := by
  let e := P.baseChangeFirstCyclesEquiv T
  constructor
  · rintro ⟨m, hm, hv⟩
    let z : LinearMap.ker (AlgebraicGeometry.Quotients.FiniteDescent.ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex R T S).f.hom := ⟨m, hm⟩
    refine ⟨(e z).val, (e z).property, ?_⟩
    have hb : (P.equivalence.inv.τ₁.hom.baseChange T) (e z).val = m :=
      congrArg Subtype.val (e.symm_apply_apply z)
    exact (scalarFunctionalBaseChange_comp T v P.equivalence.inv.τ₁.hom (e z).val).trans
      ((congrArg (Normalized.KernelBaseChange.scalarFunctionalBaseChange T v) hb).trans hv)
  · rintro ⟨m, hm, hv⟩
    let z : LinearMap.ker (AlgebraicGeometry.Quotients.FiniteDescent.ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex R T P.complex).f.hom := ⟨m, hm⟩
    refine ⟨(e.symm z).val, (e.symm z).property, ?_⟩
    exact (scalarFunctionalBaseChange_comp T v P.equivalence.inv.τ₁.hom m).symm.trans hv

theorem normalized_minimal_section_equations
    (T : Type u) [CommRing T] [Algebra R T]
    {I : Type*} (b : Module.Basis I R P.complex.X₂)
    (e : R ≃ₗ[R] P.complex.X₁) (v : S.X₁ →ₗ[R] R)
    (hv : IsUnit (minimalSectionFunctional P v (e 1))) :
    (∃ m : T ⊗[R] S.X₁, S.f.hom.baseChange T m = 0 ∧
      Normalized.KernelBaseChange.scalarFunctionalBaseChange T v m = 1) ↔
      Ideal.span (Set.range fun i => b.repr (P.complex.f (e 1)) i) ≤
        RingHom.ker (algebraMap R T) :=
  (normalized_minimal_cycles_iff P T v).trans
    (Normalized.KernelBaseChange.normalized_rankOne_kernel_equations T b e P.complex.f.hom
      (minimalSectionFunctional P v) hv)

end

end OAI.RepresentationTheory.Theta.Geometric.MinimalNormalizedSections
