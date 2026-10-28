import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Local Unramified Fiber Reflection -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.LocalUnramifiedFiberReflection.Geometric

noncomputable section

/-! For a local map of local rings, vanishing of a finite module on
the closed ground-field fiber forces it to vanish. Applied to actual
relative differentials, this reflects formal unramifiedness from the
closed fiber without a flatness assumption. -/

open scoped TensorProduct

universe u
variable (R B : Type u) [CommRing R] [CommRing B] [IsLocalRing R] [IsLocalRing B]
    [Algebra R B] [IsLocalHom (algebraMap R B)]

theorem localAlgebraModule_subsingleton_of_closedFiber
    (M : Type u) [AddCommGroup M] [Module B M] [Module R M] [IsScalarTower R B M]
    [Module.Finite B M] [Subsingleton (IsLocalRing.ResidueField R ⊗[R] M)] : Subsingleton M := by
  let k := IsLocalRing.ResidueField R
  let l := IsLocalRing.ResidueField B
  let : Algebra R l := ((IsLocalRing.residue B).comp (algebraMap R B)).toAlgebra
  let : IsScalarTower R B l := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra k l := (IsLocalRing.ResidueField.map (algebraMap R B)).toAlgebra
  let : IsScalarTower R k l := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact (IsLocalRing.ResidueField.map_residue (algebraMap R B) r).symm)
  let : Subsingleton (l ⊗[k] (k ⊗[R] M)) := inferInstance
  let : Subsingleton (l ⊗[R] M) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R k k l M).surjective.subsingleton
  have hs : Subsingleton (l ⊗[B] M) :=
    (TensorProduct.mapOfCompatibleSMul_surjective B R R l M).subsingleton
  exact (IsLocalRing.subsingleton_tensorProduct (R := B) (M := M)).mp hs

theorem localAlgebra_formallyUnramified_of_closedFiber [Algebra.EssFiniteType R B]
    [Algebra.FormallyUnramified (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] B)] :
    Algebra.FormallyUnramified R B := by
  let k := IsLocalRing.ResidueField R
  let : Algebra B (k ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  let : Subsingleton (k ⊗[R] Ω[B⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquivBase R k B (k ⊗[R] B)).injective.subsingleton
  exact ⟨localAlgebraModule_subsingleton_of_closedFiber R B Ω[B⁄R]⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.LocalUnramifiedFiberReflection.Geometric
