import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PeriodNaturality
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Circle
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TateProducts
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Period Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PeriodCoordinates

noncomputable section

/-! Full integral period coordinates identify the canonical completed
period map with the actual Tate module of the torus quotient. -/

open scoped TensorProduct Classical

variable (q : ℕ) [Fact q.Prime]
  {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Module ℚ V] [IsScalarTower ℚ ℝ V]
  (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
  [Fintype I] (b : Module.Basis I ℤ L)

def periodCircleCoordinates : (V ⧸ L.toAddSubgroup) ≃+ (I → UnitAddCircle) :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (congrArg Submodule.toAddSubgroup (b.ofZLatticeBasis_span ℝ L))).symm.trans
      (AbelianModuli.ReferenceFamily.TorsionCongruence.TorusTorsion.basisTorusEquiv (b.ofZLatticeBasis ℝ L))

omit [Module ℚ V] [IsScalarTower ℚ ℝ V] in
theorem periodCircleCoordinates_mk (v : V) (i : I) :
    periodCircleCoordinates L b (QuotientAddGroup.mk' L.toAddSubgroup v) i =
      ((b.ofZLatticeBasis ℝ L).equivFun v i : UnitAddCircle) := rfl

theorem periodCircleCoordinates_division_basis (n : ℕ) (i j : I) :
    periodCircleCoordinates L b (PeriodMap.periodDivisionPoint q L n (b i)) j =
      if j = i then ZMod.toAddCircle (1 : ZMod (q ^ n)) else 0 := by
  classical
  change periodCircleCoordinates L b
    (QuotientAddGroup.mk' L.toAddSubgroup (((q : ℚ) ^ n)⁻¹ • (b i).val)) j = _
  rw [periodCircleCoordinates_mk]
  have hs := congrFun (((b.ofZLatticeBasis ℝ L).equivFun.restrictScalars ℚ).map_smul
    (((q : ℚ) ^ n)⁻¹) (b i).val) j
  change (b.ofZLatticeBasis ℝ L).equivFun (((q : ℚ) ^ n)⁻¹ • (b i).val) j =
    ((q : ℚ) ^ n)⁻¹ • (b.ofZLatticeBasis ℝ L).equivFun (b i).val j at hs
  rw [hs, ← Module.Basis.ofZLatticeBasis_apply ℝ L b i, Module.Basis.equivFun_self]
  by_cases hji : j = i
  · subst j
    simp only [ite_true]
    calc
      _ = ((1 / (q : ℝ) ^ n : ℝ) : UnitAddCircle) := by congr 1; simp
      _ = ZMod.toAddCircle (1 : ZMod (q ^ n)) := by
        simpa using (ZMod.toAddCircle_natCast (N := q ^ n) 1).symm
  · simp [hji, Ne.symm hji]

def periodTateCoordinateEquiv :
    Add.Tate.Module (H := V ⧸ L.toAddSubgroup) q ≃ₗ[ℤ_[q]] (I → ℤ_[q]) :=
  (TateProducts.Tate.mapEquiv q (periodCircleCoordinates L b)).trans
    ((TateProducts.Tate.piEquiv q (fun _ : I => UnitAddCircle)).trans
      (LinearEquiv.piCongrRight fun _ => (Circle.circleTateEquiv q).symm))

omit [Module ℚ V] [IsScalarTower ℚ ℝ V] in
theorem periodTateCoordinateEquiv_level (t : Add.Tate.Module (H := V ⧸ L.toAddSubgroup) q)
    (i : I) (n : ℕ) :
    ZMod.toAddCircle (PadicInt.toZModPow n (periodTateCoordinateEquiv q L b t i)) =
      periodCircleCoordinates L b (t.val n).val i := by
  have h := (Circle.circleTateEquiv q).apply_symm_apply
    ((TateProducts.Tate.piEquiv q (fun _ : I => UnitAddCircle))
      (Add.Tate.map q (periodCircleCoordinates L b).toAddMonoidHom t) i)
  exact congrArg (fun z : Add.Tate.Module (H := UnitAddCircle) q => (z.val n).val) h

theorem periodTateCoordinateEquiv_basis (i : I) :
    periodTateCoordinateEquiv q L b (PeriodMap.periodTateMap q L (b i)) = Pi.single i 1 := by
  funext j
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  apply ZMod.toAddCircle_injective
  rw [periodTateCoordinateEquiv_level]
  change periodCircleCoordinates L b (PeriodMap.periodDivisionPoint q L n (b i)) j = _
  rw [periodCircleCoordinates_division_basis]
  by_cases hji : j = i
  · subst j
    simp only [Pi.single_eq_same, ite_true]
    rw [(PadicInt.toZModPow n).map_one]
  · simp only [Pi.single_eq_of_ne hji, ite_eq_right hji, map_zero]

theorem completedPeriodTateMap_coordinates :
    (periodTateCoordinateEquiv q L b).toLinearMap.comp (PeriodNaturality.completedPeriodTateMap q L) =
      (b.baseChange ℤ_[q]).equivFun.toLinearMap := by
  apply (b.baseChange ℤ_[q]).ext
  intro i
  simp only [LinearMap.comp_apply, Module.Basis.baseChange_apply]
  rw [PeriodNaturality.completedPeriodTateMap_tmul, one_smul, LinearEquiv.coe_coe, periodTateCoordinateEquiv_basis]
  funext j
  rw [← Module.Basis.baseChange_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_self]
  simp only [Pi.single_apply, eq_comm]

include b in
theorem completedPeriodTateMap_bijective : Function.Bijective (PeriodNaturality.completedPeriodTateMap q L) := by
  have hc (z : ℤ_[q] ⊗[ℤ] L) := LinearMap.congr_fun (completedPeriodTateMap_coordinates q L b) z
  constructor
  · intro x y hxy
    apply (b.baseChange ℤ_[q]).equivFun.injective
    exact (hc x).symm.trans ((congrArg (periodTateCoordinateEquiv q L b) hxy).trans (hc y))
  · intro y
    obtain ⟨x, hx⟩ := (b.baseChange ℤ_[q]).equivFun.surjective (periodTateCoordinateEquiv q L b y)
    exact ⟨x, (periodTateCoordinateEquiv q L b).injective ((hc x).trans hx)⟩

def completedPeriodTateEquiv :
    ℤ_[q] ⊗[ℤ] L ≃ₗ[ℤ_[q]] Add.Tate.Module (H := V ⧸ L.toAddSubgroup) q :=
  LinearEquiv.ofBijective (PeriodNaturality.completedPeriodTateMap q L) (completedPeriodTateMap_bijective q L b)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PeriodCoordinates
