import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.MarkingFiberTransport
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyQuotientFibers
import OAI.RepresentationTheory.Theta.Geometric.TateComparison

/-! # Concrete Shift Fiber -/

namespace OAI.RepresentationTheory.Theta.Geometric.ConcreteShiftFiber

noncomputable section

/-! The actual central graph and universal marking comparison determine
its action on every original geometric PEL fiber, including every iterate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.MarkingFiberTransport

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hg : D.HasIntegralModelGeometry) (hgood : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : TateComparison.Action D) (hA : A.IsRealization D hg hgood hIsogenyQuotient)
    {k : Type} [Field k] {b : Spec (.of k) ⟶ Spec (.of K)}

include hA in
theorem actual_shift_fiber (x : D.GeometricPoint b) :
    Nonempty (AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso
      ((D.fiberFamily b x).shiftMarking (ZMod.unitOfCoprime q hgood.2.2.1))
      (D.fiberFamily b (x ≫ A.shift.hom))) := by
  obtain ⟨j, _, _⟩ := hA.central
  obtain ⟨e, he, ht⟩ := hA.graph
  let c := x ≫ e.inv
  have hc : c ≫ (D.correspondence (AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType.central s)).source = x := by
    rw [← he]
    change (x ≫ e.inv) ≫ e.hom = x
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hct : c ≫ (D.correspondence (AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType.central s)).target = x ≫ A.shift.hom := by
    rw [ht, ← Category.assoc, he, hc]
  exact ⟨AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso.markingFiberTransport (ZMod.unitOfCoprime q hgood.2.2.1)
    j c.left (D.sourceFamilyFiberIso _ x c hc)
      (D.targetFamilyFiberIso _ (x ≫ A.shift.hom) c hct)⟩

include hA in
theorem actual_shift_iterate_fiber (x : D.GeometricPoint b) (n : ℕ) :
    Nonempty (AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso
      ((D.fiberFamily b x).shiftMarking ((ZMod.unitOfCoprime q hgood.2.2.1) ^ n))
      (D.fiberFamily b ((fun z : D.GeometricPoint b => z ≫ A.shift.hom)^[n] x))) := by
  induction n with
  | zero =>
    simp only [pow_zero, AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData.shiftMarking_one, Function.iterate_zero, id_eq]
    exact ⟨AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso.refl _⟩
  | succ n ih =>
    obtain ⟨i⟩ := ih
    obtain ⟨j⟩ := actual_shift_fiber D hg hgood hIsogenyQuotient A hA
      ((fun z : D.GeometricPoint b => z ≫ A.shift.hom)^[n] x)
    have h := (i.shiftMarking (ZMod.unitOfCoprime q hgood.2.2.1)).trans j
    rw [AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData.shiftMarking_mul, ← pow_succ'] at h
    simpa only [Function.iterate_succ_apply'] using Nonempty.intro h

end

end OAI.RepresentationTheory.Theta.Geometric.ConcreteShiftFiber
