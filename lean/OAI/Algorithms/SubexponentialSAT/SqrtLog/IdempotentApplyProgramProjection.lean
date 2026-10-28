import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramProjection

namespace OAI.Algorithms

/-! Projection invariant for sparse Horner application. It permits the native
product to truncate after every multiplication while retaining exactly the
canonical projection of the complete indicator polynomial. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open scoped BigOperators
open LeafProgram

variable {C A R : Type*} [CommRing A] [CommRing R]

def tripleAlgebra (alg : Algebra R) (decode : C → R) (h : R) (v : Triple C) : R :=
  alg.add (alg.mul (alg.add (alg.mul (decode v.c) h) (decode v.b)) h) (decode v.a)

def descendingAlgebra (alg : Algebra R) (decode : C → R) (h g : R)
    (vs : List (Triple C)) (acc : R) : R :=
  vs.foldl (fun current v => alg.add (alg.mul current g) (tripleAlgebra alg decode h v)) acc

theorem tripleAlgebra_projected (project : R →+ R)
    (hprod : ∀ x y, project (project x * project y)=project (x*y))
    (decode : C → A) (φ : A →+* R) (h : R) (v : Triple C) :
    tripleAlgebra (projectedAlgebra project) (fun c => project (φ (decode c)))
      (project h) v=project (tripleValue decode φ h v) := by
  unfold tripleAlgebra projectedAlgebra
  dsimp only
  rw [hprod,←map_add project (φ (decode v.c)*h) (φ (decode v.b)),hprod,←map_add]
  congr 1
  unfold tripleValue
  ring

theorem descendingAlgebra_projected (project : R →+ R)
    (hprod : ∀ x y, project (project x * project y)=project (x*y))
    (decode : C → A) (φ : A →+* R) (h g : R) (vs : List (Triple C)) (acc : R) :
    descendingAlgebra (projectedAlgebra project) (fun c => project (φ (decode c)))
      (project h) (project g) vs (project acc)=
        project (descendingValue decode φ h g vs acc) := by
  induction vs generalizing acc with
  | nil => rfl
  | cons v vs ih =>
    simp only [descendingAlgebra,List.foldl_cons,descendingValue]
    rw [tripleAlgebra_projected project hprod]
    change descendingAlgebra (projectedAlgebra project) (fun c => project (φ (decode c)))
      (project h) (project g) vs
      (project (project acc*project g)+project (tripleValue decode φ h v)) = _
    rw [hprod,←map_add,ih]
    congr 2
    ring

theorem apply_projected (project : R →+ R)
    (hprod : ∀ x y, project (project x * project y)=project (x*y))
    (ops : SubexpSymbolicCost.RepresentedRing C A) (φ : A →+* R)
    (h u : R) (t : ℕ) (code : RingProgram.Code C (3*t)) :
    descendingAlgebra (projectedAlgebra project) (fun c => project (φ (ops.decode c)))
      (project h) (project (u*IdempotentProgram.hValue h))
      (List.ofFn (coefficientTriple t code)).reverse 0 =
      project (∑ s : Fin t,
        u^s.val * (IdempotentProgram.digitPolynomial ops code s).eval₂ φ h *
          IdempotentProgram.hValue h^s.val) := by
  have he:=descendingAlgebra_projected project hprod ops.decode φ h
    (u*IdempotentProgram.hValue h) (List.ofFn (coefficientTriple t code)).reverse 0
  simpa only [map_zero,apply_coefficients] using he

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
