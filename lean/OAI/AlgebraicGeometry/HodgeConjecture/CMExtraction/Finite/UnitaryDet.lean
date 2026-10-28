import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.UnitaryEntries
import OAI.RepresentationTheory.Theta.Adelic.RationalSU

/-! # Unitary Det -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.UnitaryDet.Approximation

noncomputable section

section

/-! Assemble the local unitary matrices over the completed quadratic
algebra. Equality and multiplication are checked at every actual place. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.IntegralTopology OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.RationalSU

variable (F : Type) [Field F] [NumberField F] (d : F)

def finiteQuadraticEvaluation (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) :
    RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d) →+* RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inr v) :=
  RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange
    (RestrictedProduct.evalRingHom (fun w : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F => w.adicCompletion F) v)
    (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d)

theorem finiteQuadraticEvaluation_rational (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) (z : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d) :
    finiteQuadraticEvaluation F d v (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) d z) =
      RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d (.inr v) z := rfl

theorem finiteQuadraticEvaluation_ext
    {z w : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d)}
    (h : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, finiteQuadraticEvaluation F d v z = finiteQuadraticEvaluation F d v w) :
    z = w := by
  apply QuadraticAlgebra.ext
  · apply RestrictedProduct.ext
    intro v
    exact congrArg QuadraticAlgebra.re (h v)
  · apply RestrictedProduct.ext
    intro v
    exact congrArg QuadraticAlgebra.im (h v)

theorem finiteQuadraticMatrix_ext {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d))}
    (h : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, A.map (finiteQuadraticEvaluation F d v) =
      B.map (finiteQuadraticEvaluation F d v)) : A = B := by
  apply Matrix.ext
  intro i j
  apply finiteQuadraticEvaluation_ext F d
  intro v
  exact congr_fun (congr_fun (h v) i) j

variable {d} {n : ℕ} (H : (Matrix (Fin n) (Fin n) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)

local instance finiteSUOne : One (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H) :=
  ⟨⟨fun _ => 1, Filter.Eventually.of_forall (fun v => (RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H.val (.inr v)).one_mem)⟩⟩

def finiteSUQuadraticMatrix (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H) :
    Matrix (Fin n) (Fin n) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d)) :=
  fun i j => ⟨UnitaryEntries.Approximation.finiteSUCoordinate F H true i j g, UnitaryEntries.Approximation.finiteSUCoordinate F H false i j g⟩

theorem finiteSUQuadraticMatrix_evaluation (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H) (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) :
    (finiteSUQuadraticMatrix F H g).map (finiteQuadraticEvaluation F d v) = (g v).val.val := by
  apply Matrix.ext
  intro i j
  apply QuadraticAlgebra.ext <;> rfl

theorem finiteSUQuadraticMatrix_one : finiteSUQuadraticMatrix F H 1 = 1 := by
  apply finiteQuadraticMatrix_ext F d
  intro v
  rw [finiteSUQuadraticMatrix_evaluation,
    Matrix.map_one _ (map_zero (finiteQuadraticEvaluation F d v)) (map_one (finiteQuadraticEvaluation F d v))]
  rfl

theorem finiteSUQuadraticMatrix_mul (g h : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H) :
    finiteSUQuadraticMatrix F H (g * h) = finiteSUQuadraticMatrix F H g * finiteSUQuadraticMatrix F H h := by
  apply finiteQuadraticMatrix_ext F d
  intro v
  rw [finiteSUQuadraticMatrix_evaluation, Matrix.map_mul,
    finiteSUQuadraticMatrix_evaluation, finiteSUQuadraticMatrix_evaluation]
  rfl

def finiteSUQuadraticMatrixHom : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H →*
    Matrix (Fin n) (Fin n) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d)) where
  toFun := finiteSUQuadraticMatrix F H
  map_one' := finiteSUQuadraticMatrix_one F H
  map_mul' := finiteSUQuadraticMatrix_mul F H

theorem finiteSUQuadraticMatrix_continuous : Continuous (finiteSUQuadraticMatrix F H) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  rw [RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_iff]
  exact ⟨UnitaryEntries.Approximation.finiteSUCoordinate_continuous F H true i j, UnitaryEntries.Approximation.finiteSUCoordinate_continuous F H false i j⟩

theorem finiteSUQuadraticMatrix_rational (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H.val) :
    finiteSUQuadraticMatrix F H (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU F H g) =
      g.val.val.map (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) d) := by
  apply finiteQuadraticMatrix_ext F d
  intro v
  rw [finiteSUQuadraticMatrix_evaluation]
  apply Matrix.ext
  intro i j
  exact (finiteQuadraticEvaluation_rational F d v (g.val.val i j)).symm

end

section

/-! The assembled adelic matrices are actual units; both matrix and
inverse vary continuously in the original restricted unitary topology. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.IntegralTopology OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.RationalSU

variable (F : Type) [Field F] [NumberField F] {n : ℕ} {d : F}
  (H : (Matrix (Fin n) (Fin n) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)

theorem finiteSU_topologicalGroup : IsTopologicalGroup (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H) := by
  let : Fact (∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, IsOpen (RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H.val (.inr v) :
      Set (RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v))))) :=
    ⟨fun v => RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral_open F H.val (.inr v)⟩
  infer_instance

def finiteSUQuadraticUnits : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H →*
    (Matrix (Fin n) (Fin n) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d)))ˣ :=
  (finiteSUQuadraticMatrixHom F H).toHomUnits

theorem finiteSUQuadraticUnits_matrix (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H) :
    (finiteSUQuadraticUnits F H g).val = finiteSUQuadraticMatrix F H g := rfl

theorem finiteSUQuadraticUnits_inverse (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H) :
    (finiteSUQuadraticUnits F H g).inv = finiteSUQuadraticMatrix F H (g⁻¹) := rfl

theorem finiteSUQuadraticUnits_continuous : Continuous (finiteSUQuadraticUnits F H) := by
  let := finiteSU_topologicalGroup F H
  apply Units.continuous_iff.mpr
  constructor
  · exact finiteSUQuadraticMatrix_continuous F H
  · exact (finiteSUQuadraticMatrix_continuous F H).comp continuous_inv

theorem finiteSUQuadraticUnits_evaluation (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H) (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) :
    Units.map (finiteQuadraticEvaluation F d v).mapMatrix.toMonoidHom (finiteSUQuadraticUnits F H g) =
      (g v).val := by
  apply Units.ext
  exact finiteSUQuadraticMatrix_evaluation F H g v

theorem finiteSUQuadraticUnits_rational (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H.val) :
    finiteSUQuadraticUnits F H (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU F H g) =
      Units.map (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) d).mapMatrix.toMonoidHom g.val := by
  apply Units.ext
  exact finiteSUQuadraticMatrix_rational F H g

end

/-! The completed matrices preserve the original Hermitian form and
determinant. Both identities follow from their actual local values. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.IntegralTopology OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.RationalSU

variable (F : Type) [Field F] [NumberField F] (d : F)

theorem finiteQuadraticEvaluation_star (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F)
    (z : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d)) :
    finiteQuadraticEvaluation F d v (star z) = star (finiteQuadraticEvaluation F d v z) := by
  apply QuadraticAlgebra.ext
  · change (star z).re v = (star (finiteQuadraticEvaluation F d v z)).re
    simp only [QuadraticAlgebra.re_star, zero_mul, add_zero]
    rfl
  · change (star z).im v = (star (finiteQuadraticEvaluation F d v z)).im
    simp only [QuadraticAlgebra.im_star]
    rfl

theorem finiteQuadraticEvaluation_matrix {n : ℕ} (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F)
    (A : Matrix (Fin n) (Fin n) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)) :
    (A.map (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) d)).map
      (finiteQuadraticEvaluation F d v) = RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F A (.inr v) := by
  apply Matrix.ext
  intro i j
  exact finiteQuadraticEvaluation_rational F d v (A i j)

variable {d} {n : ℕ} (H : (Matrix (Fin n) (Fin n) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)

def finiteHermitianMatrix :
    Matrix (Fin n) (Fin n) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) d)) :=
  H.val.map (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) d)

theorem finiteSUQuadraticUnits_preserves (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H) :
    (finiteSUQuadraticUnits F H g).val.conjTranspose * finiteHermitianMatrix F H *
      (finiteSUQuadraticUnits F H g).val = finiteHermitianMatrix F H := by
  apply finiteQuadraticMatrix_ext F d
  intro v
  change (((finiteSUQuadraticMatrix F H g).conjTranspose *
    (H.val.map (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) d))) *
      finiteSUQuadraticMatrix F H g).map (finiteQuadraticEvaluation F d v) = _
  rw [Matrix.map_mul, Matrix.map_mul,
    RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.map_conjTranspose _ (finiteQuadraticEvaluation_star F d v),
    finiteSUQuadraticMatrix_evaluation, finiteQuadraticEvaluation_matrix]
  exact (g v).property.1

theorem finiteSUQuadraticUnits_det (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H) :
    Matrix.GeneralLinearGroup.det (finiteSUQuadraticUnits F H g) = 1 := by
  apply Units.ext
  change (finiteSUQuadraticMatrix F H g).det = 1
  apply finiteQuadraticEvaluation_ext F d
  intro v
  rw [(finiteQuadraticEvaluation F d v).map_det]
  change ((finiteSUQuadraticMatrix F H g).map (finiteQuadraticEvaluation F d v)).det =
    finiteQuadraticEvaluation F d v 1
  rw [finiteSUQuadraticMatrix_evaluation, map_one]
  exact congrArg Units.val (g v).property.2

def finiteAdelicUnitary : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H →ₜ* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (finiteHermitianMatrix F H) where
  toFun g := ⟨finiteSUQuadraticUnits F H g,
    finiteSUQuadraticUnits_preserves F H g, finiteSUQuadraticUnits_det F H g⟩
  map_one' := by apply Subtype.ext; exact map_one (finiteSUQuadraticUnits F H)
  map_mul' g h := by apply Subtype.ext; exact map_mul (finiteSUQuadraticUnits F H) g h
  continuous_toFun := (finiteSUQuadraticUnits_continuous F H).subtype_mk _

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.UnitaryDet.Approximation
