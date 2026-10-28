import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResolutionLocalExact
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Resolution Local Cokernel -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResolutionLocalCokernel

noncomputable section

/-! Flat extension preserves the middle exactness of a projective
resolution and identifies its degree-zero cokernel with the extended module. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R) (P : ProjectiveResolution M)

def cokernelEquiv : (P.complex.X 0 ⧸ (P.complex.d 1 0).hom.range) ≃ₗ[R] M :=
  (Submodule.quotEquivOfEq _ _ P.exact₀.moduleCat_range_eq_ker).trans
    ((P.π.f 0).hom.quotKerEquivOfSurjective
      ((ModuleCat.epi_iff_surjective _).mp inferInstance))

variable (S : Type u) [CommRing S] [Algebra R S] [Module.Flat R S]

theorem exact :
    (ComplexDeterminantBaseChange.complex R S (P.complex.d 2 1).hom
      (P.complex.d 1 0).hom (ModuleCat.hom_ext_iff.mp (P.complex.d_comp_d 2 1 0))).Exact := by
  let Q := (ProjectionFormula.Flat.Extension.baseChange R S).mapProjectiveResolution P
  exact Q.exact_succ 0

theorem length :
    Module.length S ((S ⊗[R] P.complex.X 0) ⧸ ((P.complex.d 1 0).hom.baseChange S).range) =
      Module.length S (S ⊗[R] M) := by
  let F := ProjectionFormula.Flat.Extension.baseChange R S
  exact (cokernelEquiv S (F.obj M) (F.mapProjectiveResolution P)).length_eq

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResolutionLocalCokernel
