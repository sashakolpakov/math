import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Zero Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.ZeroKernel

noncomputable section

/-! Degree-zero cohomology of a nonnegative complex is its first differential kernel; quasi-isomorphisms give the corresponding actual linear equivalence. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {R : Type u} [CommRing R]

def cochainZeroCyclesIso (C : CochainComplex (ModuleCat.{v} R) ℕ) :
    C.cycles 0 ≅ ModuleCat.of R (C.d 0 1).hom.ker :=
  C.cyclesIsoSc' 0 0 1 (by simp) (by simp) ≪≫ (C.sc' 0 0 1).moduleCatCyclesIso

def cochainZeroHomologyKernelEquiv (C : CochainComplex (ModuleCat.{v} R) ℕ) :
    C.homology 0 ≃ₗ[R] (C.d 0 1).hom.ker :=
  (C.isoHomologyπ₀.symm ≪≫ cochainZeroCyclesIso C).toLinearEquiv

def cochainZeroKernelEquivOfQuasiIso {C D : CochainComplex (ModuleCat.{v} R) ℕ}
    (φ : C ⟶ D) [QuasiIsoAt φ 0] : (C.d 0 1).hom.ker ≃ₗ[R] (D.d 0 1).hom.ker :=
  (cochainZeroHomologyKernelEquiv C).symm.trans
    ((isoOfQuasiIsoAt φ 0).toLinearEquiv.trans (cochainZeroHomologyKernelEquiv D))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.ZeroKernel
