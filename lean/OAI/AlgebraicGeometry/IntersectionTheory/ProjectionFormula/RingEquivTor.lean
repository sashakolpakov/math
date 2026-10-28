import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DerivedBaseChange
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ScalarQuotient
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! # Ring Equiv Tor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RingEquivTor

noncomputable section

/-! Native Tor and its module lengths transport through a ring
isomorphism by the actual restriction-of-scalars equivalence. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)

def tensorEquiv (M N : ModuleCat.{u} S) :
    ((ModuleCat.restrictScalars e.toRingHom).obj M) ⊗[R]
      ((ModuleCat.restrictScalars e.toRingHom).obj N) ≃ₗ[R]
        (ModuleCat.restrictScalars e.toRingHom).obj (M ⊗ N) := by
  let : Algebra R S := e.toRingHom.toAlgebra
  let : Module R M := Module.compHom M e.toRingHom
  let : Module R N := Module.compHom N e.toRingHom
  let : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  let : IsScalarTower R S N := IsScalarTower.of_compHom R S N
  let : TensorProduct.CompatibleSMul R S M N :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective M N e.surjective
  exact TensorProduct.equivOfCompatibleSMul S R R M N

def tensorIso (M : ModuleCat.{u} S) :
    ModuleCat.restrictScalars e.toRingHom ⋙ tensorLeft ((ModuleCat.restrictScalars e.toRingHom).obj M) ≅
      tensorLeft M ⋙ ModuleCat.restrictScalars e.toRingHom :=
  NatIso.ofComponents (fun N => (tensorEquiv e M N).toModuleIso) (by
    intro N N' f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m n
    rfl)

def torIso (M N : ModuleCat.{u} S) (n : ℕ) :
    ((Tor (ModuleCat R) n).obj ((ModuleCat.restrictScalars e.toRingHom).obj M)).obj
      ((ModuleCat.restrictScalars e.toRingHom).obj N) ≅
        (ModuleCat.restrictScalars e.toRingHom).obj (((Tor (ModuleCat S) n).obj M).obj N) :=
  DerivedBaseChange.leftDerivedIso (tensorLeft M)
    (tensorLeft ((ModuleCat.restrictScalars e.toRingHom).obj M))
    (ModuleCat.restrictScalars e.toRingHom) (ModuleCat.restrictScalars e.toRingHom)
    (tensorIso e M) N n

theorem length (M N : ModuleCat.{u} S) (n : ℕ) :
    Module.length R (((Tor (ModuleCat R) n).obj ((ModuleCat.restrictScalars e.toRingHom).obj M)).obj
      ((ModuleCat.restrictScalars e.toRingHom).obj N)) =
      Module.length S (((Tor (ModuleCat S) n).obj M).obj N) := by
  rw [(torIso e M N n).toLinearEquiv.length_eq]
  let T := ((Tor (ModuleCat S) n).obj M).obj N
  let : Algebra R S := e.toRingHom.toAlgebra
  let : Module R T := Module.compHom T e.toRingHom
  let : IsScalarTower R S T := IsScalarTower.of_compHom R S T
  change Module.length R T = Module.length S T
  exact Module.length_eq_of_surjective e.surjective

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RingEquivTor
