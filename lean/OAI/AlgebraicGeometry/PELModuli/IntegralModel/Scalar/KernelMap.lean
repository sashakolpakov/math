import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Kernel Map -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Scalar.KernelMap

noncomputable section

/-! The canonical map from scalar extension of a differential kernel
to the kernel after scalar extension, with exactness and generator formulas. -/

open _root_.CategoryTheory
open scoped ChangeOfRings

universe u

def scalarKernelMap {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) {M N : ModuleCat.{u} R} (d : M ⟶ N) :
    (ModuleCat.extendScalars f).obj (ModuleCat.of R d.hom.ker) →ₗ[A]
      ((ModuleCat.extendScalars f).map d).hom.ker :=
  (d.hom.shortComplexKer.map (ModuleCat.extendScalars f)).moduleCatToCycles

theorem scalarKernelMap_surjective {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) {M N : ModuleCat.{u} R} (d : M ⟶ N)
    (h : (d.hom.shortComplexKer.map (ModuleCat.extendScalars f)).Exact) :
    Function.Surjective (scalarKernelMap f d) :=
  (ShortComplex.exact_iff_surjective_moduleCatToCycles _).mp h

theorem scalarKernelMap_one_val {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) {M N : ModuleCat.{u} R} (d : M ⟶ N) (x : d.hom.ker) :
    (scalarKernelMap f d ((1 : A) ⊗ₜ[R,f] x)).val = (1 : A) ⊗ₜ[R,f] x.val := by
  exact ModuleCat.ExtendScalars.map_tmul _ _ _ _

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Scalar.KernelMap
