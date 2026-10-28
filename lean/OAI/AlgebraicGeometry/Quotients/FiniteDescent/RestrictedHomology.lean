import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.RingTheory.Finiteness.Basic

/-! # Restricted Homology -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.RestrictedHomology

noncomputable section

/-! Finiteness of homology can be recovered from its restriction of scalars. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace Construction.RestrictedHomologyFinite

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
variable (C : CochainComplex (ModuleCat.{u} S) ℕ)

def iso (q : ℕ) :
    (((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology q ≅
      (ModuleCat.restrictScalars f).obj (C.homology q) :=
  (C.sc q).mapHomologyIso (ModuleCat.restrictScalars f)

theorem finite {D : CochainComplex (ModuleCat.{u} R) ℕ}
    (e : D ≅ ((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj C)
    (q : ℕ) [Module.Finite R (D.homology q)] : Module.Finite S (C.homology q) := by
  let B := C.homology q
  let : Algebra R S := f.toAlgebra
  let : Module R B := Module.compHom B f
  have : IsScalarTower R S B := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let i := HomologicalComplex.homologyMapIso e q ≪≫ iso f C q
  have : Module.Finite R B := Module.Finite.of_surjective i.toLinearEquiv.toLinearMap
    i.toLinearEquiv.surjective
  exact Module.Finite.of_restrictScalars_finite R S B

end Construction.RestrictedHomologyFinite

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.RestrictedHomology
