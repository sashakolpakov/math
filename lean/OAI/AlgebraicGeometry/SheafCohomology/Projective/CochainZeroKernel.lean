import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Cochain Zero Kernel -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.CochainZeroKernel

noncomputable section

/-! Degree-zero cohomology is the actual kernel of the first cochain differential. -/

open _root_.CategoryTheory
universe u v

def cochainHZeroLinearEquivKernel {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{v} R) ℕ) :
    K.homology 0 ≃ₗ[R] (K.d 0 1).hom.ker :=
  ((K.isoHomologyπ 0 0 (by simp) (by simp)).symm ≪≫
    K.cyclesIsoSc' 0 0 1 (by simp) (by simp) ≪≫
    (K.sc' 0 0 1).cyclesIsoKernel ≪≫ ModuleCat.kernelIsoKer (K.d 0 1)).toLinearEquiv

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.CochainZeroKernel
