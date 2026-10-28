import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice

/-! # Integral Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps

noncomputable section

section

/-! Actual algebraic group maps act on rational period spaces. These
maps are functorial and faithful, without a cohomological comparison
hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods

variable {A B C : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property

theorem linearLift_preserves_rational (f : A.toOver ⟶ B.toOver) [IsMonHom f]
    (v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) (hv : v ∈ RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) : Maps.IntrinsicLinearMaps.linearLift f v ∈ RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B := by
  induction hv using Submodule.span_induction with
  | mem v hv => exact Submodule.subset_span (Maps.IntrinsicLinearMaps.linearLift_preserves f v hv)
  | zero => exact (Maps.IntrinsicLinearMaps.linearLift f).map_zero.symm ▸ (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B).zero_mem
  | add v w _ _ hv hw =>
      exact ((Maps.IntrinsicLinearMaps.linearLift f).map_add v w).symm ▸ (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B).add_mem hv hw
  | smul q v _ hv =>
      exact (((Maps.IntrinsicLinearMaps.linearLift f).restrictScalars ℚ).map_smul q v).symm ▸
        (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B).smul_mem q hv

def rationalLift (f : A.toOver ⟶ B.toOver) [IsMonHom f] :
    RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A →ₗ[ℚ] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B :=
  (((Maps.IntrinsicLinearMaps.linearLift f).restrictScalars ℚ).domRestrict (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)).codRestrict
    (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B) (fun v => linearLift_preserves_rational f v.val v.property)

theorem rationalLift_congr (f h : A.toOver ⟶ B.toOver) [IsMonHom f] [IsMonHom h]
    (e : f = h) : rationalLift f = rationalLift h := by
  cases e
  rfl

theorem rationalLift_coe (f : A.toOver ⟶ B.toOver) [IsMonHom f] (v : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    (rationalLift f v).val = Maps.IntrinsicLinearMaps.linearLift f v.val := rfl

theorem rationalLift_comp (f : A.toOver ⟶ B.toOver) (h : B.toOver ⟶ C.toOver)
    [IsMonHom f] [IsMonHom h] : rationalLift (f ≫ h) = (rationalLift h).comp (rationalLift f) := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact LinearMap.congr_fun (Maps.IntrinsicLinearMaps.linearLift_comp f h) v.val

theorem rationalLift_id (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : rationalLift (𝟙 A.toOver) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact LinearMap.congr_fun (Maps.IntrinsicLinearMaps.linearLift_id A) v.val

def rationalLiftIso (e : A.toOver ≅ B.toOver) [IsMonHom e.hom] :
    RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A ≃ₗ[ℚ] RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B :=
  LinearEquiv.ofLinearMap (rationalLift e.hom) (rationalLift e.inv)
    ((rationalLift_comp e.inv e.hom).symm.trans
      ((rationalLift_congr _ _ e.inv_hom_id).trans (rationalLift_id B)))
    ((rationalLift_comp e.hom e.inv).symm.trans
      ((rationalLift_congr _ _ e.hom_inv_id).trans (rationalLift_id A)))

/-- The rational period representation is faithful on actual algebraic
group morphisms, since the integral marking spans the real tangent space. -/
theorem rationalLift_faithful (f h : A.toOver ⟶ B.toOver) [IsMonHom f] [IsMonHom h]
    (he : rationalLift f = rationalLift h) : f = h := by
  apply Maps.IntrinsicLinearMaps.linearLift_faithful f h
  let : IsZLattice ℝ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) := HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice_full Maps.IntrinsicAlgebraicMaps.algebraization A
  have hreal : (Maps.IntrinsicLinearMaps.linearLift f).restrictScalars ℝ = (Maps.IntrinsicLinearMaps.linearLift h).restrictScalars ℝ := by
    apply (RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A).ext
    intro i
    have hi := congrArg (fun v : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B => v.val)
      (LinearMap.congr_fun he (RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A i))
    change Maps.IntrinsicLinearMaps.linearLift f (RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A i).val = Maps.IntrinsicLinearMaps.linearLift h (RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A i).val at hi
    rw [RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis_coe] at hi
    have hb : RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A i = (Torsion.IntrinsicTorsion.periodBasis A i).val :=
      Module.Basis.ofZLatticeBasis_apply ℝ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (Torsion.IntrinsicTorsion.periodBasis A) i
    exact (congrArg (Maps.IntrinsicLinearMaps.linearLift f) hb).trans (hi.trans (congrArg (Maps.IntrinsicLinearMaps.linearLift h) hb).symm)
  exact LinearMap.ext (fun v => LinearMap.congr_fun hreal v)

end

/-! Native rational lifts preserve the actual integral lattice, and
their congruence equations are exactly the equations on the original
complex exponential periods. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods

variable {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}

theorem rationalLift_integral (f : A.toOver ⟶ B.toOver) [IsMonHom f]
    (v : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) (hv : v ∈ RationalLattice.IntrinsicRationalPeriods.integralPeriods A) :
    rationalLift f v ∈ RationalLattice.IntrinsicRationalPeriods.integralPeriods B := Maps.IntrinsicLinearMaps.linearLift_preserves f v.val hv

theorem rationalLiftIso_integral_iff (e : A.toOver ≅ B.toOver) [IsMonHom e.hom]
    (v : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) : rationalLiftIso e v ∈ RationalLattice.IntrinsicRationalPeriods.integralPeriods B ↔ v ∈ RationalLattice.IntrinsicRationalPeriods.integralPeriods A := by
  constructor
  · intro hv
    have hw := rationalLift_integral e.inv (rationalLiftIso e v) hv
    exact (congrArg (fun x : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A => x ∈ RationalLattice.IntrinsicRationalPeriods.integralPeriods A)
      ((rationalLiftIso e).symm_apply_apply v)).mp hw
  · exact rationalLift_integral e.hom v

theorem native_congruence_iff_rational (f : A.toOver ⟶ A.toOver) [IsMonHom f] (N : ℕ) :
    (∀ v ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A, ∃ w ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A, Maps.IntrinsicLinearMaps.linearLift f v - v = (N : ℤ) • w) ↔
      ∀ v ∈ RationalLattice.IntrinsicRationalPeriods.integralPeriods A, ∃ w ∈ RationalLattice.IntrinsicRationalPeriods.integralPeriods A, rationalLift f v - v = (N : ℤ) • w := by
  constructor
  · intro h v hv
    obtain ⟨w, hw, he⟩ := h v.val hv
    exact ⟨⟨w, Submodule.subset_span hw⟩, hw, Subtype.ext he⟩
  · intro h v hv
    let v' : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A := ⟨v, Submodule.subset_span hv⟩
    obtain ⟨w, hw, he⟩ := h v' hv
    exact ⟨w.val, hw, congrArg (fun x : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A => x.val) he⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps
