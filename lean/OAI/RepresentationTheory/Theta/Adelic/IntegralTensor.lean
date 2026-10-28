import OAI.RepresentationTheory.Theta.Adelic.GlobalFrameIntegral
import OAI.RepresentationTheory.Theta.Adelic.IntegralModulus

/-! # Integral Tensor -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.IntegralTensor.Coordinates

/-! Conjugating an integral quadratic tensor matrix by the actual
compatible frame gives an integral symplectic-coordinate matrix, with
an integral inverse. -/

open _root_.Matrix
open scoped Classical Kronecker

open OAI.RepresentationTheory.Theta.Adelic.IntegralModulus OAI.RepresentationTheory.Theta.Adelic.GlobalFrameIntegral

section Algebra
variable {k : Type} [Field k] {d : k} {n m : ℕ}
variable (H : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))
variable (K : Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))
variable (P : Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d n m H K)

def coordinateTensorEquiv (U : (Matrix (Fin n × Fin m) (Fin n × Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) :
    Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := k) n m ≃ₗ[k] Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := k) n m :=
  P.coordinates.symm.trans (((Matrix.GeneralLinearGroup.toLin U).toLinearEquiv.restrictScalars k).trans P.coordinates)

def coordinateTensorUnit (U : (Matrix (Fin n × Fin m) (Fin n × Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) :
    (Matrix (Fin (n * m) ⊕ Fin (n * m)) (Fin (n * m) ⊕ Fin (n * m)) k)ˣ where
  val := LinearMap.toMatrix' (coordinateTensorEquiv H K P U).toLinearMap
  inv := LinearMap.toMatrix' (coordinateTensorEquiv H K P U).symm.toLinearMap
  val_inv := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  inv_val := by
    rw [← LinearMap.toMatrix'_comp]
    simp

theorem coordinateTensorUnit_dualPair (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K) :
    (coordinateTensorUnit H K P (Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits g.1.val g.2.val)).val =
      (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H K P g).val := rfl

theorem coordinateTensorUnit_difference (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K)
    (U : (Matrix (Fin n × Fin m) (Fin n × Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
    (hU : U.val = (Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits g.1.val g.2.val).val - 1) :
    (coordinateTensorUnit H K P U).val = (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H K P g).val - 1 := by
  ext i j
  change P.coordinates (U.val *ᵥ (P.coordinates.symm (Pi.single j 1))) i =
    P.coordinates ((Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits g.1.val g.2.val).val *ᵥ (P.coordinates.symm (Pi.single j 1))) i -
      (1 : Matrix _ _ k) i j
  rw [hU, Matrix.sub_mulVec, Matrix.one_mulVec, map_sub, LinearEquiv.apply_symm_apply]
  simp only [Pi.sub_apply, Pi.single_apply, Matrix.one_apply]

theorem tensorUnits_first_difference
    (g u : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (hu : u.val = g.val - 1) :
    (Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits u (1 : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)).val =
      (Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits g (1 : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)).val - 1 := by
  change u.val ⊗ₖ (1 : Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) = g.val ⊗ₖ 1 - 1
  rw [hu]
  have he : (g.val - 1) ⊗ₖ (1 : Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) =
      g.val ⊗ₖ (1 : Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) -
        (1 : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) ⊗ₖ (1 : Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) := by
    apply Matrix.ext
    intro i j
    exact sub_mul (g.val i.1 j.1) ((1 : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) i.1 j.1)
      ((1 : Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) i.2 j.2)
  rw [he, Matrix.one_kronecker_one]

theorem tensorUnits_second_difference
    (g u : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (hu : u.val = g.val - 1) :
    (Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits (1 : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) u).val =
      (Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits (1 : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) g).val - 1 := by
  change (1 : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) ⊗ₖ u.val = 1 ⊗ₖ g.val - 1
  rw [hu]
  have he : (1 : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) ⊗ₖ (g.val - 1) =
      (1 : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) ⊗ₖ g.val -
        (1 : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) ⊗ₖ (1 : Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) := by
    apply Matrix.ext
    intro i j
    exact mul_sub ((1 : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) i.1 j.1) (g.val i.2 j.2)
      ((1 : Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) i.2 j.2)
  rw [he, Matrix.one_kronecker_one]

end Algebra

variable (F : Type) [Field F] [NumberField F] (d : F) (n m : ℕ)
variable (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d n m H K) (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F)
variable (hP : GlobalFrameIntegral.IntegralFrameAt F d n m H K P v)

include hP in
theorem coordinateTensorUnit_integral
    (U : (Matrix (Fin n × Fin m) (Fin n × Fin m) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (hv : ∀ i j, U.val i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v)
    (hi : ∀ i j, U.inv i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v) :
    (∀ i j, (coordinateTensorUnit (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H v).val (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K v).val (P.localFrame v) U).val i j ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v) ∧
    (∀ i j, (coordinateTensorUnit (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H v).val (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K v).val (P.localFrame v) U).inv i j ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v) := by
  have hb (j : Fin (n * m) ⊕ Fin (n * m)) : ∀ i,
      (P.localFrame v).coordinates.symm (Pi.single j 1) i ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v := by
    apply hP.fromPhase
    intro i
    by_cases h : i = j <;> simp [h]
  constructor
  · intro i j
    change (P.localFrame v).coordinates (U.val *ᵥ ((P.localFrame v).coordinates.symm (Pi.single j 1))) i ∈ _
    exact hP.toPhase _ (IntegralModulus.integral_mulVec _ hv (hb j)) i
  · intro i j
    change (P.localFrame v).coordinates (U.inv *ᵥ ((P.localFrame v).coordinates.symm (Pi.single j 1))) i ∈ _
    exact hP.toPhase _ (IntegralModulus.integral_mulVec _ hi (hb j)) i

end RepresentationTheory.Theta.Adelic.IntegralTensor.Coordinates

namespace RepresentationTheory.Theta.Adelic.IntegralTensor.OpenCell

/-! Integral inverse matrices for the two actual tensor open-cell
differences, in the chosen local symplectic frame. -/

open _root_.Matrix
open scoped Classical Kronecker

open OAI.RepresentationTheory.Theta.Adelic.GlobalFrameIntegral OAI.RepresentationTheory.Theta.Adelic.IntegralTensor.Coordinates

section Algebra
variable {R I J : Type*} [CommRing R] [DecidableEq I] [DecidableEq J] (S : Subring R)

theorem integral_one : ∀ i j : I, (1 : Matrix I I R) i j ∈ S := by
  intro i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

omit [DecidableEq I] [DecidableEq J] in
theorem integral_kronecker {A : Matrix I I R} {B : Matrix J J R}
    (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S) :
    ∀ i j, (A ⊗ₖ B) i j ∈ S := fun i j => S.mul_mem (hA i.1 j.1) (hB i.2 j.2)

end Algebra

variable (F : Type) [Field F] [NumberField F] (d : F) (n m : ℕ)
variable (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d n m H K) (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F)

def firstDifference (u : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ) :=
  Coordinates.coordinateTensorUnit (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H v).val (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K v).val (P.localFrame v)
    (Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits u (1 : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ))

def secondDifference (u : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ) :=
  Coordinates.coordinateTensorUnit (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H v).val (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K v).val (P.localFrame v)
    (Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits (1 : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ) u)

theorem firstDifference_val (g : Weil.AdelicSplitting.Integral.Construction.LocalUnitary F H.val v)
    (u : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ) (hu : u.val = g.val.val - 1) :
    (firstDifference F d n m H K P v u).val = (Weil.AdelicSplitting.Assembly.Construction.localDualAction F d n m H K P v (g, 1)).val - 1 :=
  Coordinates.coordinateTensorUnit_difference _ _ _ (g, 1) _ (Coordinates.tensorUnits_first_difference g.val u hu)

theorem secondDifference_val (g : Weil.AdelicSplitting.Integral.Construction.LocalUnitary F K.val v)
    (u : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ) (hu : u.val = g.val.val - 1) :
    (secondDifference F d n m H K P v u).val = (Weil.AdelicSplitting.Assembly.Construction.localDualAction F d n m H K P v (1, g)).val - 1 :=
  Coordinates.coordinateTensorUnit_difference _ _ _ (1, g) _ (Coordinates.tensorUnits_second_difference g.val u hu)

variable (hP : GlobalFrameIntegral.IntegralFrameAt F d n m H K P v)

include hP in
theorem firstDifference_integral (u : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (hu : ∀ i j, u.val i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v) (hi : ∀ i j, u.inv i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v) :
    (∀ i j, (firstDifference F d n m H K P v u).val i j ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v) ∧
    (∀ i j, (firstDifference F d n m H K P v u).inv i j ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v) :=
  Coordinates.coordinateTensorUnit_integral F d n m H K P v hP _
    (integral_kronecker _ hu (integral_one _)) (integral_kronecker _ hi (integral_one _))

include hP in
theorem secondDifference_integral (u : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (hu : ∀ i j, u.val i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v) (hi : ∀ i j, u.inv i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v) :
    (∀ i j, (secondDifference F d n m H K P v u).val i j ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v) ∧
    (∀ i j, (secondDifference F d n m H K P v u).inv i j ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v) :=
  Coordinates.coordinateTensorUnit_integral F d n m H K P v hP _
    (integral_kronecker _ (integral_one _) hu) (integral_kronecker _ (integral_one _) hi)

end RepresentationTheory.Theta.Adelic.IntegralTensor.OpenCell

namespace RepresentationTheory.Theta.Adelic.IntegralTensor.PairAction

/-! The actual dual-pair symplectic action preserves the standard
integral phase lattice in every integral compatible frame. -/

open Filter
open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.GlobalFrameIntegral
open OAI.RepresentationTheory.Theta.Adelic.IntegralTensor.Coordinates OAI.RepresentationTheory.Theta.Adelic.IntegralTensor.OpenCell

variable (F : Type) [Field F] [NumberField F] (d : F) (n m : ℕ)
variable (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d n m H K) (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F)

theorem localDualAction_integral (hP : GlobalFrameIntegral.IntegralFrameAt F d n m H K P v) :
    Set.MapsTo (Weil.AdelicSplitting.Assembly.Construction.localDualAction F d n m H K P v) (Weil.AdelicSplitting.Integral.Construction.localPairIntegral F H.val K.val v)
      (Weil.AdelicSplitting.Vacuum.Construction.symplecticIntegral F (n * m) v) := by
  have hval (g : Weil.AdelicSplitting.Integral.Construction.LocalUnitary F H.val v × Weil.AdelicSplitting.Integral.Construction.LocalUnitary F K.val v)
      (hg : g ∈ Weil.AdelicSplitting.Integral.Construction.localPairIntegral F H.val K.val v) :
      ∀ i j, (Weil.AdelicSplitting.Assembly.Construction.localDualAction F d n m H K P v g).val i j ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v := by
    have h := Coordinates.coordinateTensorUnit_integral F d n m H K P v hP (Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits g.1.val g.2.val)
      (OpenCell.integral_kronecker _ hg.1.1 hg.2.1) (OpenCell.integral_kronecker _ hg.1.2 hg.2.2)
    exact h.1
  intro g hg
  constructor
  · exact hval g hg
  · change ∀ i j, ((Weil.AdelicSplitting.Assembly.Construction.localDualAction F d n m H K P v g)⁻¹).val i j ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v
    rw [← map_inv]
    exact hval g⁻¹ ((Weil.AdelicSplitting.Integral.Construction.localPairIntegral F H.val K.val v).inv_mem hg)

theorem localizedUnit_integral_eventually {r : ℕ}
    (A : (Matrix (Fin r) (Fin r) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ) :
    ∀ᶠ v in cofinite,
      (∀ i j, (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d A v).val i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v) ∧
      (∀ i j, (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d A v).inv i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v) := by
  have hv : ∀ᶠ v in cofinite, ∀ i j,
      Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v (A.val i j) ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal_integral F d _
  have hi : ∀ᶠ v in cofinite, ∀ i j,
      Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v (A.inv i j) ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal_integral F d _
  filter_upwards [hv, hi] with v hv hi
  exact ⟨hv, hi⟩

end RepresentationTheory.Theta.Adelic.IntegralTensor.PairAction

end

end OAI
