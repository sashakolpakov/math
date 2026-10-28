import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExternalTensorRankOne
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTensorNaturality
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AdditiveFreeVanishing
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.ExactSequence

/-! # External Tensor Acyclic -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExternalTensorAcyclic

noncomputable section

/-! External products of finite free modules are acyclic for tensoring
with the diagonal. The rank-one case follows from one-sided flat Tor
base change; additivity supplies the general finite free case. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  ExternalTensorFunctor.scalar ExternalTensorFunctor.tower ExternalTensor.module

theorem right_flat (K A B : Type u) [Field K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] :
    Module.Flat B (A ⊗[K] B) :=
  Module.Flat.of_linearEquiv (Algebra.TensorProduct.commRight K B A).symm.toLinearEquiv

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTensor OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTensorNaturality

variable (K R : Type u) [Field K] [CommRing R] [Algebra K R]

local instance : SMul R (DiagonalTensor.Ring K R) := (Algebra.TensorProduct.rightAlgebra (R := K) (A := R) (B := R)).toSMul
local instance : Module R (DiagonalTensor.Ring K R) := (Algebra.TensorProduct.rightAlgebra (R := K) (A := R) (B := R)).toModule

local instance : Module R (DiagonalTensorNaturality.diagonal K R) := Module.restrictScalars R (DiagonalTensor.Ring K R) (DiagonalTensorNaturality.diagonal K R)
local instance : IsScalarTower R (DiagonalTensor.Ring K R) (DiagonalTensorNaturality.diagonal K R) :=
  IsScalarTower.restrictScalars R (DiagonalTensor.Ring K R) (DiagonalTensorNaturality.diagonal K R)

def diagonalRightEquiv : DiagonalTensorNaturality.diagonal K R ≃ₗ[R] R :=
  { AddEquiv.refl R with
    map_smul' := by
      intro r x
      change ((1 * r) * (show R from x)) = r * (show R from x)
      rw [one_mul] }

theorem rank_one (N : ModuleCat.{u} R) (i : ℕ) :
    IsZero (((Tor (ModuleCat (DiagonalTensor.Ring K R)) (i + 1)).obj
      ((ExternalTensorFunctor.tensor K R R N).obj (.of R R))).obj (DiagonalTensorNaturality.diagonal K R)) := by
  let : Module.Flat R (DiagonalTensor.Ring K R) := right_flat K R R
  let : Module.Flat R (DiagonalTensorNaturality.diagonal K R) := Module.Flat.of_linearEquiv (diagonalRightEquiv K R)
  have hz := OneSidedTor.higher_isZero R (DiagonalTensor.Ring K R) N (DiagonalTensorNaturality.diagonal K R) i
  let e := ExternalTensorRankOne.equiv K R R N
  let e₀ := ExternalTensor.congr K R R (M := (ModuleCat.of R R)) (M' := R) (N := N) (N' := N)
    (mK := ExternalTensorFunctor.scalar K R (.of R R))
    (mTower := ExternalTensorFunctor.tower K R (.of R R))
    (mK' := inferInstanceAs (Module K R))
    (LinearEquiv.refl R R) (LinearEquiv.refl R N)
  let F := (Tor (ModuleCat (DiagonalTensor.Ring K R)) (i + 1)).flip.obj (DiagonalTensorNaturality.diagonal K R)
  exact IsZero.of_iso hz (F.mapIso (e₀ ≪≫ e.symm.toModuleIso))

theorem free (N : ModuleCat.{u} R) (P : ModuleCat.{u} R) [Module.Free R P] [Module.Finite R P] (i : ℕ) :
    IsZero (((Tor (ModuleCat (DiagonalTensor.Ring K R)) (i + 1)).obj
      ((ExternalTensorFunctor.tensor K R R N).obj P)).obj (DiagonalTensorNaturality.diagonal K R)) :=
  AdditiveFreeVanishing.isZero R
    (ExternalTensorFunctor.tensor K R R N ⋙
      ((Tor (ModuleCat (DiagonalTensor.Ring K R)) (i + 1)).flip.obj (DiagonalTensorNaturality.diagonal K R)))
    (rank_one K R N i) P

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExternalTensorAcyclic
