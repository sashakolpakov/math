import OAI.RepresentationTheory.Theta.Geometric.Cleared.FiberMarking
import OAI.RepresentationTheory.Theta.Geometric.Cleared.ReferencePELIsogeny

/-! # Generic Isogeny -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Exact cleared reference isogenies give actual isogenies between the
original universal geometric fibers, with the actual iterated central target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {x y : D.domain}
    (R : D.ReferencePELPointData hg x) (S : D.ReferencePELPointData hg y)
    (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (A : TateComparison.Action D.pel)
    (hA : A.IsRealization D.pel hg hgood hIsogenyQuotient)
    (n : ℕ)

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.family Data.ActiveHeckeThetaData.ReferencePELPointData.genericFamilyIso
  AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.fiberFamily

def Data.ActiveHeckeThetaData.clearedReferenceGenericIsogeny
    (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny R.family
      (S.family.shiftMarking (ZMod.unitOfCoprime (q ^ n) (hgood.2.2.1.pow_left n))) (q ^ (2 * n))) :
    AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny
      (D.pel.fiberFamily (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ≫ D.pel.complexGenericPoint) R.genericPoint)
      (D.pel.fiberFamily (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ≫ D.pel.complexGenericPoint)
        ((fun z => z ≫ A.shift.hom)^[n] S.genericPoint)) (q ^ (2 * n)) :=
  e.transport R.genericFamilyIso (S.clearedMarking_actual_fiber hgood hIsogenyQuotient A hA n).some

end

end OAI.RepresentationTheory.Theta.Geometric
