import OAI.Analysis.PDE.Dirichlet.Fourth.FieldPeriodic
import OAI.Analysis.PDE.Elliptic.Boundary.FieldRemainder
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Stability
import OAI.Analysis.PDE.Dirichlet.HolderApproxSpace

/-! Removing the prescribed boundary value in the second tangent equation. -/

noncomputable section
open Set Filter Module
open scoped Topology Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Nonlinear OAI.Analysis.PDE.Elliptic OAI.LinearAlgebra.Moore OAI.Analysis.Normed.Function.Holder

local instance fourthBackgroundFirstGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fourthBackgroundFirstSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fourthBackgroundSecondGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthBackgroundSecondSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem indexedNondivergence_sub {I : Type*} [Fintype I] [DecidableEq I]
    (A : EuclideanSpace ℝ I → Matrix I I ℝ) (u v : EuclideanSpace ℝ I → ℝ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (x : EuclideanSpace ℝ I) :
    indexedNondivergenceOperator A (fun y => u y - v y) x =
      indexedNondivergenceOperator A u x - indexedNondivergenceOperator A v x := by
  unfold indexedNondivergenceOperator
  rw [OAI.Analysis.PDE.Schauder.second_fderiv_sub u v hu hv x]
  simp only [sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem contDiff_indexedNondivergence {I : Type*} [Fintype I] [DecidableEq I]
    (A : EuclideanSpace ℝ I → Matrix I I ℝ) (u : EuclideanSpace ℝ I → ℝ)
    (hA : ContDiff ℝ 1 A) (hu : ContDiff ℝ 3 u) :
    ContDiff ℝ 1 (indexedNondivergenceOperator A u) := by
  have hH : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) :=
    (hu.fderiv_right (m := 2) (by norm_num)).fderiv_right (by norm_num)
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact (contDiff_pi.mp (contDiff_pi.mp hA i) j).mul
    ((hH.clm_apply contDiff_const).clm_apply contDiff_const)

def mooreSecondBackgroundForcing {n : ℕ} (u B f : CoordinateSpace n 4 → ℝ)
    (T S : CoordinateSpace n 4 → CoordinateSpace n 4) (x : CoordinateSpace n 4) : ℝ :=
  mooreSecondFieldForcing u f T S x -
    indexedNondivergenceOperator (fun y => mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y))
      (OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative B T) S) x

theorem moore_second_background_equation {n : ℕ} (u B f : CoordinateSpace n 4 → ℝ)
    (T S : CoordinateSpace n 4 → CoordinateSpace n 4)
    (hu : ContDiff ℝ 4 u) (hB : ContDiff ℝ 4 B)
    (hT : ContDiff ℝ 3 T) (hS : ContDiff ℝ 2 S) (hf : ContDiff ℝ 1 f)
    (x : CoordinateSpace n 4)
    (heq : (fun y => OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) =ᶠ[𝓝 x] f) :
    mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u)
      (OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative (fun y => u y - B y) T) S) x =
        mooreSecondBackgroundForcing u B f T S x := by
  have huT : ContDiff ℝ 3 (OAI.Analysis.PDE.Elliptic.fieldDerivative u T) := OAI.Analysis.PDE.Elliptic.contDiff_fieldDerivative hu hT (by norm_num)
  have hBT : ContDiff ℝ 3 (OAI.Analysis.PDE.Elliptic.fieldDerivative B T) := OAI.Analysis.PDE.Elliptic.contDiff_fieldDerivative hB hT (by norm_num)
  have huTS : ContDiff ℝ 2 (OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative u T) S) :=
    OAI.Analysis.PDE.Elliptic.contDiff_fieldDerivative huT hS (by norm_num)
  have hBTS : ContDiff ℝ 2 (OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative B T) S) :=
    OAI.Analysis.PDE.Elliptic.contDiff_fieldDerivative hBT hS (by norm_num)
  rw [OAI.Analysis.PDE.Elliptic.fieldDerivative_sub (hu.differentiable (by norm_num)) (hB.differentiable (by norm_num)),
    OAI.Analysis.PDE.Elliptic.fieldDerivative_sub (huT.differentiable (by norm_num)) (hBT.differentiable (by norm_num)),
    ← mooreRealMatrix_linearization_at _ (huTS.sub hBTS).contDiffAt,
    indexedNondivergence_sub _ _ _ huTS hBTS x,
    moore_second_field_equation u f T S hu hT hS hf x heq]
  rfl

theorem contDiff_mooreSecondBackgroundForcing {n : ℕ} (u B f : CoordinateSpace n 4 → ℝ)
    (T S : CoordinateSpace n 4 → CoordinateSpace n 4)
    (hu : ContDiff ℝ 4 u) (hB : ContDiff ℝ 5 B) (hf : ContDiff ℝ 3 f)
    (hT : ContDiff ℝ 4 T) (hS : ContDiff ℝ 3 S) :
    ContDiff ℝ 1 (mooreSecondBackgroundForcing u B f T S) := by
  have hBT : ContDiff ℝ 4 (OAI.Analysis.PDE.Elliptic.fieldDerivative B T) := OAI.Analysis.PDE.Elliptic.contDiff_fieldDerivative hB hT (by norm_num)
  have hBTS : ContDiff ℝ 3 (OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative B T) S) :=
    OAI.Analysis.PDE.Elliptic.contDiff_fieldDerivative hBT hS (by norm_num)
  exact (contDiff_mooreSecondFieldForcing u f T S hu hf hT hS).sub
    (contDiff_indexedNondivergence _ _ ((contDiff_mooreRealMatrix _ 1).comp
      (OAI.Analysis.PDE.Green.contDiff_quaternionHessian_one OAI.Analysis.Calculus.Quaternion.fourSlots (hu.of_le (by norm_num)))) hBTS)

variable {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

omit [Fintype ι] in
theorem periodic_mooreSecondBackgroundForcing {n : ℕ}
    {e : CoordinateSpace n 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
    {u B f : CoordinateSpace n 4 → ℝ} {T S : CoordinateSpace n 4 → CoordinateSpace n 4}
    (hu : LatticePeriodic e b u) (hB : LatticePeriodic e b B) (hf : LatticePeriodic e b f)
    (hT : LatticePeriodic e b T) (hS : LatticePeriodic e b S) :
    LatticePeriodic e b (mooreSecondBackgroundForcing u B f T S) := by
  intro x l
  unfold mooreSecondBackgroundForcing
  rw [periodic_mooreSecondFieldForcing hu hf hT hS x l,
    periodic_indexedNondivergence ((hu.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots).comp mooreRealMatrix)
      ((hB.fieldDerivative hT).fieldDerivative hS) x l]

theorem exists_periodic_second_background_forcing {n : ℕ}
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K) {r : CoordinateSpace n 4 → ℝ}
    (hr : Continuous r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (u B f : CoordinateSpace n 4 → ℝ) (T S : CoordinateSpace n 4 → CoordinateSpace n 4)
    (hu : ContDiff ℝ 4 u) (hB : ContDiff ℝ 5 B) (hf : ContDiff ℝ 3 f)
    (hT : ContDiff ℝ 4 T) (hS : ContDiff ℝ 3 S)
    (hup : LatticePeriodic e b u) (hBp : LatticePeriodic e b B) (hfp : LatticePeriodic e b f)
    (hTp : LatticePeriodic e b T) (hSp : LatticePeriodic e b S)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ F : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := {x | r x ≤ 0}) (α := α) e b,
      ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value F.val x = mooreSecondBackgroundForcing u B f T S x := by
  have hp := periodic_mooreSecondBackgroundForcing hup hBp hfp hTp hSp
  obtain ⟨F, hF⟩ := exists_periodic_holder_field e b hK hr hrp hbounded _
    (contDiff_mooreSecondBackgroundForcing u B f T S hu hB hf hT hS) hp hα hα1
  refine ⟨⟨F, ?_⟩, hF⟩
  exact latticePeriodic_restriction_zeroExtension e b (hrp.comp (fun t => t ≤ 0))
    _ hp (OAI.Analysis.Normed.Function.Holder.HolderMap.value F) hF

end OAI.Analysis.PDE.Dirichlet
