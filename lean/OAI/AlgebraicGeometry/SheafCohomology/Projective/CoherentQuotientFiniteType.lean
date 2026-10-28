import OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent
import OAI.AlgebraicGeometry.SheafCohomology.Projective.AffineSectionExact

/-! # Coherent Quotient Finite Type -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.CoherentQuotientFiniteType

noncomputable section

open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules

/-! Quasicoherent quotients of finite-type module sheaves remain of finite type. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite OAI.AlgebraicGeometry.SheafCohomology.Projective.AffineSectionExact
universe u
namespace Scheme.Modules

theorem isFiniteType_of_epi {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent] (f : M ⟶ N) [Epi f] :
    N.IsFiniteType := by
  have : (kernel f).IsQuasicoherent := Quasicoherent.Scheme.Modules.isQuasicoherent_kernel f
  let T := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hT : T.ShortExact := ShortComplex.ShortExact.mk (ShortComplex.kernelSequence_exact f)
  apply Quasicoherent.Scheme.Modules.isFiniteType_of_sections_module_finite N
  intro U
  let : Module.Finite Γ(X, U.1) Γ(M, U.1) :=
    Quasicoherent.Scheme.Modules.sections_module_finite_of_isFiniteType_of_isAffineOpen M U
  let fU : Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(N, U.1) := (f.val.app (op U.1)).hom
  exact Module.Finite.of_surjective fU
    (AffineSectionExact.affineSections_surjective_of_shortExact hT U.1 U.2)

theorem isFiniteType_cokernel {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] [N.IsFiniteType] (f : M ⟶ N) :
    (cokernel f).IsFiniteType := by
  have := Quasicoherent.Scheme.Modules.isQuasicoherent_cokernel f
  exact isFiniteType_of_epi (cokernel.π f)

end Scheme.Modules

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.CoherentQuotientFiniteType
