import OAI.Analysis.PDE.Dirichlet.Fourth.FieldBackground
import OAI.Analysis.PDE.Dirichlet.ClassicalLinearUpgrade

/-! Noncircular boundary regularity of second tangent derivatives. The
classical derivative is only C² a priori; the actual Dirichlet inverse and
uniqueness give its closed C²,α jet. -/

noncomputable section
open Set Filter Module
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Nonlinear OAI.Analysis.PDE.Elliptic OAI.LinearAlgebra.Moore OAI.Analysis.Normed.Function.Holder

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]

local instance tangentRegularityFirstGroup : NormedAddCommGroup (CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance tangentRegularityFirstSpace : NormedSpace ℝ (CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance tangentRegularitySecondGroup :
    NormedAddCommGroup (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance tangentRegularitySecondSpace :
    NormedSpace ℝ (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance

omit [FiniteDimensional ℝ P] in
theorem exists_second_tangent_C2Holder
    (hn : 1 ≤ n) (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r : CoordinateSpace n 4 → ℝ} (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    [Nonempty {x | r x ≤ 0}]
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (ψ B f : CoordinateSpace n 4 → ℝ) (T S : CoordinateSpace n 4 → CoordinateSpace n 4)
    (hψ : ContDiff ℝ 4 ψ) (hB : ContDiff ℝ 5 B) (hf : ContDiff ℝ 3 f)
    (hT : ContDiff ℝ 4 T) (hS : ContDiff ℝ 3 S)
    (hψp : LatticePeriodic e b ψ) (hBp : LatticePeriodic e b B) (hfp : LatticePeriodic e b f)
    (hTp : LatticePeriodic e b T) (hSp : LatticePeriodic e b S)
    (hψpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (hbd : ∀ x, r x = 0 → ψ x = B x)
    (hTtan : ∀ x, r x = 0 → fderiv ℝ r x (T x) = 0)
    (hStan : ∀ x, r x = 0 → fderiv ℝ r x (S x) = 0)
    (heq : ∀ x, r x < 0 → OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = f x) :
    ∃ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α, U ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e b ∧
      (∀ x : {x | r x ≤ 0},
        OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative (fun y => ψ y - B y) T) S x = OAI.Analysis.Normed.Function.Holder.C2Holder.value U x) ∧
      (∀ x : {x | r x ≤ 0},
        fderiv ℝ (OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative (fun y => ψ y - B y) T) S) x =
          OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x) ∧
      (∀ x : {x | r x ≤ 0},
        fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative (fun y => ψ y - B y) T) S)) x =
          OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x) := by
  obtain ⟨F, hF⟩ := exists_periodic_second_background_forcing e b hK hr.continuous hrp hbounded
    ψ B f T S hψ hB hf hT hS hψp hBp hfp hTp hSp hα.le hα1.le
  obtain ⟨C, hC, hsolve⟩ := exists_C2Holder_classical_moore_solution (hΩD := hΩD)
    hn e b hK hr hrp hbounded hreg hrpos hα hα1 ψ (hψ.of_le (by norm_num)) hψp hψpos
  let w := OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative (fun y => ψ y - B y) T) S
  have hw : ContDiff ℝ 2 w := by
    have hd : ContDiff ℝ 3 (OAI.Analysis.PDE.Elliptic.fieldDerivative (fun y => ψ y - B y) T) :=
      OAI.Analysis.PDE.Elliptic.contDiff_fieldDerivative (hψ.sub (hB.of_le (by norm_num)))
        (hT.of_le (by norm_num)) (by norm_num)
    exact OAI.Analysis.PDE.Elliptic.contDiff_fieldDerivative hd (hS.of_le (by norm_num)) (by norm_num)
  have hsubp : LatticePeriodic e b (fun y => ψ y - B y) := by
    intro x l
    exact congrArg₂ (· - ·) (hψp x l) (hBp x l)
  have hwp : LatticePeriodic e b w := (hsubp.fieldDerivative hTp).fieldDerivative hSp
  have hwzero (x) (hx : r x = 0) : w x = 0 :=
    twice_fieldDerivative_zero_on_level (hr.of_le (by simp))
      ((hψ.of_le (by norm_num)).sub (hB.of_le (by norm_num))) (hT.of_le (by norm_num)) hreg
      (fun y hy => sub_eq_zero.mpr (hbd y hy)) hTtan hStan hx
  have hwL (x) (hx : r x < 0) : mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) w x =
      OAI.Analysis.Normed.Function.Holder.HolderMap.value F.val ⟨x, hΩD hx⟩ := by
    rw [hF]
    apply moore_second_background_equation ψ B f T S hψ (hB.of_le (by norm_num))
      (hT.of_le (by norm_num)) (hS.of_le (by norm_num)) (hf.of_le (by norm_num)) x
    filter_upwards [(isOpen_lt hr.continuous continuous_const).mem_nhds hx] with y hy
    exact heq y hy
  obtain ⟨U, hUnorm, hU, h0, h1, h2⟩ := hsolve F w hw hwp hwzero hwL
  exact ⟨U, hU, h0, h1, h2⟩

end OAI.Analysis.PDE.Dirichlet
