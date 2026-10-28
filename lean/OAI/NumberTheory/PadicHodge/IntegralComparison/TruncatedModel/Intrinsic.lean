import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinarySectionMap
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomologyComposition

/-! # Intrinsic -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Intrinsic

noncomputable section

/-! The original native cohomology input to the bounded crystalline
comparison is the canonical homology map for the composite coefficient
functor, with its two literal universe lifts. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]

instance coefficients_preservesHomology :
    (OrdinarySectionMap.Ordinary.coefficients p k n).PreservesHomology := by
  change (ModuleCat.restrictScalars (algebraMap (WittVector p k) (Truncated.Witt.Ring p k n)) ⋙
    SmoothWitt.DeRham.Comparison.coefficientFunctor p k).PreservesHomology
  infer_instance

def inputEquiv (q : ℕ) :
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total (Truncated.Witt.Ring p k n) X).homology q ≃+
      (GlobalDeRham.Comparison.complex p k n X).homology q :=
  (Witt.CoefficientCoordinates.addEquiv p k
    ((ModuleCat.restrictScalars (algebraMap (WittVector p k) (Truncated.Witt.Ring p k n))).obj
      ((AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total (Truncated.Witt.Ring p k n) X).homology q))).trans
    (AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso (OrdinarySectionMap.Ordinary.coefficients p k n)
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total (Truncated.Witt.Ring p k n) X) q).symm.toLinearEquiv.toAddEquiv

omit [Fintype k] [CharP k p] [X.left.IsSeparated] in
theorem input_eq (q : ℕ)
    (x : (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total (Truncated.Witt.Ring p k n) X).homology q) :
    (Witt.CoefficientCoordinates.cohomologyEquiv p k
      (GlobalDeRham.Comparison.rawComplex p k n X) q).symm
        ((AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso
          (ModuleCat.restrictScalars (algebraMap (WittVector p k) (Truncated.Witt.Ring p k n)))
          (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total (Truncated.Witt.Ring p k n) X) q).inv x) =
    inputEquiv p k n X q x := by
  let U := ModuleCat.restrictScalars (algebraMap (WittVector p k) (Truncated.Witt.Ring p k n))
  let F := GlobalDeRham.Comparison.coefficientFunctor p k
  let K := AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total (Truncated.Witt.Ring p k n) X
  let eU := AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso U K q
  let eF := AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso F ((U.mapHomologicalComplex (.up ℕ)).obj K) q
  let e := AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso (U ⋙ F) K q
  apply e.toLinearEquiv.injective
  change e.hom (eF.inv (ULift.up (ULift.up (eU.inv x)))) =
    e.hom (e.inv (ULift.up (ULift.up x)))
  have h := AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomologyComposition.MappedComplexHomologyComposition.complex U F K q
  calc
    _ = F.map eU.hom (eF.hom (eF.inv (ULift.up (ULift.up (eU.inv x))))) :=
      (ConcreteCategory.congr_hom h _).symm
    _ = ULift.up (ULift.up x) := by
      rw [Iso.inv_hom_id_apply]
      change ULift.up (ULift.up (eU.hom (eU.inv x))) = _
      rw [Iso.inv_hom_id_apply]
    _ = _ := (Iso.inv_hom_id_apply e _).symm

variable (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

theorem comparison (q : ℕ)
    (x : (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total (Truncated.Witt.Ring p k n) X).homology q) :
    IntrinsicCohomology.Intrinsic.comparisonEquiv p k n X Y f hp I q x =
      (GlobalDeRham.Comparison.homologyIso p k n X Y f hp I q).hom
        (inputEquiv p k n X q x) :=
  congrArg (GlobalDeRham.Comparison.homologyIso p k n X Y f hp I q).hom
    (input_eq p k n X q x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Intrinsic
