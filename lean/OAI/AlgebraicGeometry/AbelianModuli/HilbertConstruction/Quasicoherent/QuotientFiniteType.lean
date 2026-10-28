import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Cokernels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.QuasicoherentEpimorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TypeFromAffineSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentFiniteTypeSections

/-! # Quotient Finite Type -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.QuotientFiniteType

noncomputable section

/-! Quotients of finite-type quasicoherent module sheaves are finite type. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem quasicoherent_quotient_finiteType {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] [M.IsFiniteType] (f : M ⟶ N) [Epi f] :
    N.IsFiniteType := by
  apply HilbertConstruction.Finite.TypeFromAffineSections.module_finiteType_of_affine_sections_finite
  intro U
  have : Module.Finite Γ(X, U.1) Γ(M, U.1) := Affine.QuasicoherentFiniteTypeSections.affineOpen_quasicoherent_finiteType_sections_finite M U
  let g : Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(N, U.1) := (f.val.app (.op U.1)).hom
  exact Module.Finite.of_surjective g
    (AffineOpen.QuasicoherentEpimorphisms.affineOpen_quasicoherent_surjective_of_epi f U.1 U.2)

theorem quasicoherent_cokernel_finiteType {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] [N.IsFiniteType] (f : M ⟶ N) :
    (cokernel f).IsFiniteType := by
  have : (cokernel f).IsQuasicoherent := Cokernels.module_quasicoherent_cokernel f
  exact quasicoherent_quotient_finiteType (cokernel.π f)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.QuotientFiniteType
