import OAI.RepresentationTheory.Theta.Geometric.ConcreteShiftFiber
import OAI.RepresentationTheory.Theta.Geometric.Reference.GenericPELFamily

/-! # Fiber Marking -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The exact q-power marking on a reference family is the target of
the same number of iterations of the actual TateComparison central graph. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem Cleared.FiberMarking.unitOfCoprime_pow (q N n : ℕ) (h : Nat.Coprime q N) :
    ZMod.unitOfCoprime (q ^ n) (h.pow_left n) = (ZMod.unitOfCoprime q h) ^ n := by
  apply Units.ext
  simp only [ZMod.coe_unitOfCoprime, Units.val_pow_eq_pow_val, Nat.cast_pow]

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {x : D.domain}
    (R : D.ReferencePELPointData hg x)
    (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (A : TateComparison.Action D.pel)
    (hA : A.IsRealization D.pel hg hgood hIsogenyQuotient)

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.family Data.ActiveHeckeThetaData.ReferencePELPointData.genericFamilyIso AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.fiberFamily

include hA in
theorem Data.ActiveHeckeThetaData.ReferencePELPointData.clearedMarking_actual_fiber (n : ℕ) :
    Nonempty (AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso
      (R.family.shiftMarking (ZMod.unitOfCoprime (q ^ n) (hgood.2.2.1.pow_left n)))
      (D.pel.fiberFamily (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ≫ D.pel.complexGenericPoint)
        ((fun z => z ≫ A.shift.hom)^[n] R.genericPoint))) := by
  obtain ⟨j⟩ := ConcreteShiftFiber.actual_shift_iterate_fiber D.pel hg hgood hIsogenyQuotient A hA R.genericPoint n
  rw [Cleared.FiberMarking.unitOfCoprime_pow q D.pel.level n hgood.2.2.1]
  exact ⟨(R.genericFamilyIso.symm.shiftMarking ((ZMod.unitOfCoprime q hgood.2.2.1) ^ n)).trans j⟩

end

end OAI.RepresentationTheory.Theta.Geometric
