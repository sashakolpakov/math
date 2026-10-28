import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.HeadCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.ZeroKernel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.FiniteExact

/-! # Finite Cycles -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.FiniteCycles

noncomputable section

/-! Removing the augmentation of a complex preserves finite cohomology when the augmentation term and positive cohomology are finite. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

theorem shortComplex_cycles_finite (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Finite R S.homology] : Module.Finite R S.cycles := by
  let T := ShortComplex.mk S.toCycles S.homologyπ S.toCycles_comp_homologyπ
  have hT : T.Exact := ShortComplex.exact_of_g_is_cokernel T S.homologyIsCokernel
  exact Noetherian.FiniteExact.noetherian_finite_of_exact S.toCycles.hom S.homologyπ.hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp hT)

theorem cochain_tail_zero_homology_finite (C : CochainComplex (ModuleCat.{u} R) ℕ)
    [Module.Finite R (C.X 0)] [Module.Finite R (C.homology 1)] :
    Module.Finite R ((Head.CochainHead.tail C).homology 0) := by
  have : Module.Finite R (C.sc' 0 1 2).X₁ := inferInstanceAs (Module.Finite R (C.X 0))
  have : Module.Finite R (C.sc' 0 1 2).homology :=
    Module.Finite.equiv (C.homologyIsoSc' 0 1 2 (by simp) (by simp)).toLinearEquiv
  have : Module.Finite R (C.sc' 0 1 2).cycles := shortComplex_cycles_finite (C.sc' 0 1 2)
  have : Module.Finite R (C.d 1 2).hom.ker :=
    Module.Finite.equiv (C.sc' 0 1 2).moduleCatCyclesIso.toLinearEquiv
  have hd : (Head.CochainHead.tail C).d 0 1 = C.d 1 2 := Head.CochainHead.tail_d C 0 1
  have : Module.Finite R ((Head.CochainHead.tail C).d 0 1).hom.ker := hd.symm ▸ inferInstance
  exact Module.Finite.equiv (ZeroKernel.cochainZeroHomologyKernelEquiv (Head.CochainHead.tail C)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.FiniteCycles
