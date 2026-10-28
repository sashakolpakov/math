import OAI.Analysis.PDE.Dirichlet.Fourth.Equation
import OAI.Analysis.PDE.Elliptic.Boundary.FieldCalculus

/-! Two variable-field derivatives of the actual Moore equation. The source
is expressed using at most third derivatives of the potential. -/

noncomputable section
open Set Filter
open scoped Topology Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Nonlinear OAI.Analysis.PDE.Elliptic OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Green

local instance fourthFieldFirstGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fourthFieldFirstSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fourthFieldSecondGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthFieldSecondSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

section Indexed
variable {I : Type*} [Fintype I] [DecidableEq I]

def indexedFieldCorrection (A : EuclideanSpace ℝ I → Matrix I I ℝ)
    (u : EuclideanSpace ℝ I → ℝ) (T : EuclideanSpace ℝ I → EuclideanSpace ℝ I)
    (x : EuclideanSpace ℝ I) : ℝ :=
  ∑ i : I, ∑ j : I, A x i j *
    (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (fderiv ℝ T x (EuclideanSpace.single j 1)) +
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single j 1)
        (fderiv ℝ T x (EuclideanSpace.single i 1)) +
      fderiv ℝ u x (fderiv ℝ (fderiv ℝ T) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)))

theorem indexed_field_correction (A : EuclideanSpace ℝ I → Matrix I I ℝ)
    (u : EuclideanSpace ℝ I → ℝ) (T : EuclideanSpace ℝ I → EuclideanSpace ℝ I)
    (hu : ContDiff ℝ 3 u) (hT : ContDiff ℝ 2 T) (x : EuclideanSpace ℝ I) :
    indexedNondivergenceOperator A (OAI.Analysis.PDE.Elliptic.fieldDerivative u T) x =
      indexedNondivergenceOperator A (directionalDerivative u (T x)) x +
        indexedFieldCorrection A u T x := by
  unfold indexedNondivergenceOperator indexedFieldCorrection
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [OAI.Analysis.PDE.Elliptic.hessian_fieldDerivative hu hT, hessian_directionalDerivative hu]
  ring

def indexedFieldCommutator (A : EuclideanSpace ℝ I → Matrix I I ℝ)
    (u : EuclideanSpace ℝ I → ℝ) (T : EuclideanSpace ℝ I → EuclideanSpace ℝ I)
    (x : EuclideanSpace ℝ I) : ℝ :=
  indexedFieldCorrection A u T x -
    indexedNondivergenceOperator (fun y i j => OAI.Analysis.PDE.Elliptic.fieldDerivative (fun z => A z i j) T y) u x

theorem indexed_field_equation (A : EuclideanSpace ℝ I → Matrix I I ℝ)
    (u f : EuclideanSpace ℝ I → ℝ) (T : EuclideanSpace ℝ I → EuclideanSpace ℝ I)
    (hA : ContDiff ℝ 1 A) (hu : ContDiff ℝ 3 u) (hT : ContDiff ℝ 2 T)
    (x : EuclideanSpace ℝ I) (heq : indexedNondivergenceOperator A u =ᶠ[𝓝 x] f) :
    indexedNondivergenceOperator A (OAI.Analysis.PDE.Elliptic.fieldDerivative u T) x =
      OAI.Analysis.PDE.Elliptic.fieldDerivative f T x + indexedFieldCommutator A u T x := by
  have hd := congrArg (fun L : EuclideanSpace ℝ I →L[ℝ] ℝ => L (T x))
    (heq.fderiv_eq (𝕜 := ℝ))
  change directionalDerivative (indexedNondivergenceOperator A u) (T x) x = _ at hd
  rw [indexedNondivergence_directional A u hA hu] at hd
  have hc := indexed_field_correction A u T hu hT x
  have ht : indexedNondivergenceOperator
      (fun y i j => directionalDerivative (fun z => A z i j) (T x) y) u x =
      indexedNondivergenceOperator
        (fun y i j => OAI.Analysis.PDE.Elliptic.fieldDerivative (fun z => A z i j) T y) u x := rfl
  rw [ht] at hd
  unfold indexedFieldCommutator
  change _ = OAI.Analysis.PDE.Elliptic.fieldDerivative f T x at hd
  linarith

theorem contDiff_indexedFieldCorrection {k : WithTop ℕ∞}
    (A : EuclideanSpace ℝ I → Matrix I I ℝ) (u : EuclideanSpace ℝ I → ℝ)
    (T : EuclideanSpace ℝ I → EuclideanSpace ℝ I) (hA : ContDiff ℝ k A)
    (hDu : ContDiff ℝ k (fderiv ℝ u)) (hHu : ContDiff ℝ k (fderiv ℝ (fderiv ℝ u)))
    (hDT : ContDiff ℝ k (fderiv ℝ T)) (hHT : ContDiff ℝ k (fderiv ℝ (fderiv ℝ T))) :
    ContDiff ℝ k (indexedFieldCorrection A u T) := by
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact (contDiff_pi.mp (contDiff_pi.mp hA i) j).mul
    (((hHu.clm_apply contDiff_const).clm_apply (hDT.clm_apply contDiff_const)).add
      ((hHu.clm_apply contDiff_const).clm_apply (hDT.clm_apply contDiff_const)) |>.add
        (hDu.clm_apply ((hHT.clm_apply contDiff_const).clm_apply contDiff_const)))

theorem contDiff_indexedFieldCommutator
    (A : EuclideanSpace ℝ I → Matrix I I ℝ) (u : EuclideanSpace ℝ I → ℝ)
    (T : EuclideanSpace ℝ I → EuclideanSpace ℝ I) (hA : ContDiff ℝ 2 A)
    (hu : ContDiff ℝ 3 u) (hT : ContDiff ℝ 3 T) :
    ContDiff ℝ 1 (indexedFieldCommutator A u T) := by
  have hDu : ContDiff ℝ 2 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hHu : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) := hDu.fderiv_right (by norm_num)
  have hDT : ContDiff ℝ 2 (fderiv ℝ T) := hT.fderiv_right (by norm_num)
  have hHT : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ T)) := hDT.fderiv_right (by norm_num)
  apply (contDiff_indexedFieldCorrection A u T (hA.of_le (by norm_num))
    (hDu.of_le (by norm_num)) hHu (hDT.of_le (by norm_num)) hHT).sub
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact (OAI.Analysis.PDE.Elliptic.contDiff_fieldDerivative (contDiff_pi.mp (contDiff_pi.mp hA i) j)
    (hT.of_le (by norm_num)) (by norm_num)).mul
      ((hHu.clm_apply contDiff_const).clm_apply contDiff_const)

end Indexed

def mooreFirstFieldForcing {n : ℕ} (u f : CoordinateSpace n 4 → ℝ)
    (T : CoordinateSpace n 4 → CoordinateSpace n 4) (x : CoordinateSpace n 4) : ℝ :=
  OAI.Analysis.PDE.Elliptic.fieldDerivative f T x +
    indexedFieldCorrection (fun y => mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) u T x

theorem moore_first_field_equation {n : ℕ} (u f : CoordinateSpace n 4 → ℝ)
    (T : CoordinateSpace n 4 → CoordinateSpace n 4)
    (hu : ContDiff ℝ 3 u) (hT : ContDiff ℝ 2 T)
    (x : CoordinateSpace n 4) (hf : DifferentiableAt ℝ f x)
    (heq : (fun y => OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) =ᶠ[𝓝 x] f) :
    indexedNondivergenceOperator (fun y => mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y))
      (OAI.Analysis.PDE.Elliptic.fieldDerivative u T) x = mooreFirstFieldForcing u f T x := by
  rw [indexed_field_correction _ u T hu hT x]
  unfold mooreFirstFieldForcing
  congr 1
  rw [mooreRealMatrix_linearization_at _
    (contDiff_directionalDerivative hu (m := 2) (by norm_num) (T x)).contDiffAt]
  exact mooreLinearization_directional_eq hu (T x) hf heq

def mooreSecondFieldForcing {n : ℕ} (u f : CoordinateSpace n 4 → ℝ)
    (T S : CoordinateSpace n 4 → CoordinateSpace n 4) (x : CoordinateSpace n 4) : ℝ :=
  OAI.Analysis.PDE.Elliptic.fieldDerivative (mooreFirstFieldForcing u f T) S x +
    indexedFieldCommutator (fun y => mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y))
      (OAI.Analysis.PDE.Elliptic.fieldDerivative u T) S x

theorem moore_second_field_equation {n : ℕ} (u f : CoordinateSpace n 4 → ℝ)
    (T S : CoordinateSpace n 4 → CoordinateSpace n 4)
    (hu : ContDiff ℝ 4 u) (hT : ContDiff ℝ 3 T) (hS : ContDiff ℝ 2 S)
    (hf : ContDiff ℝ 1 f) (x : CoordinateSpace n 4)
    (heq : (fun y => OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) =ᶠ[𝓝 x] f) :
    indexedNondivergenceOperator (fun y => mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y))
      (OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative u T) S) x = mooreSecondFieldForcing u f T S x := by
  apply indexed_field_equation
    (fun y => mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) (OAI.Analysis.PDE.Elliptic.fieldDerivative u T)
    (mooreFirstFieldForcing u f T) S
    ((contDiff_mooreRealMatrix n 1).comp
      (OAI.Analysis.PDE.Green.contDiff_quaternionHessian_one OAI.Analysis.Calculus.Quaternion.fourSlots (hu.of_le (by norm_num))))
    (OAI.Analysis.PDE.Elliptic.contDiff_fieldDerivative hu hT (by norm_num)) hS x
  filter_upwards [heq.eventuallyEq_nhds] with y hy
  exact moore_first_field_equation u f T (hu.of_le (by norm_num))
    (hT.of_le (by norm_num)) y (hf.differentiable one_ne_zero y) hy

theorem contDiff_mooreSecondFieldForcing {n : ℕ} (u f : CoordinateSpace n 4 → ℝ)
    (T S : CoordinateSpace n 4 → CoordinateSpace n 4)
    (hu : ContDiff ℝ 4 u) (hf : ContDiff ℝ 3 f)
    (hT : ContDiff ℝ 4 T) (hS : ContDiff ℝ 3 S) :
    ContDiff ℝ 1 (mooreSecondFieldForcing u f T S) := by
  have hA : ContDiff ℝ 2 (fun y => mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) :=
    (contDiff_mooreRealMatrix n 2).comp (contDiff_quaternionHessian_two OAI.Analysis.Calculus.Quaternion.fourSlots hu)
  have hDu : ContDiff ℝ 3 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hHu : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ u)) := hDu.fderiv_right (by norm_num)
  have hDT : ContDiff ℝ 3 (fderiv ℝ T) := hT.fderiv_right (by norm_num)
  have hHT : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ T)) := hDT.fderiv_right (by norm_num)
  have hfirst : ContDiff ℝ 2 (mooreFirstFieldForcing u f T) :=
    (OAI.Analysis.PDE.Elliptic.contDiff_fieldDerivative hf (hT.of_le (by norm_num)) (by norm_num)).add
      (contDiff_indexedFieldCorrection _ u T hA (hDu.of_le (by norm_num)) hHu
        (hDT.of_le (by norm_num)) hHT)
  exact (OAI.Analysis.PDE.Elliptic.contDiff_fieldDerivative hfirst (hS.of_le (by norm_num)) (by norm_num)).add
    (contDiff_indexedFieldCommutator _ (OAI.Analysis.PDE.Elliptic.fieldDerivative u T) S hA
      (OAI.Analysis.PDE.Elliptic.contDiff_fieldDerivative hu (hT.of_le (by norm_num)) (by norm_num)) hS)

end OAI.Analysis.PDE.Dirichlet
