import OAI.AlgebraicGeometry.PELModuli.IntegralModel.QuasicoherentPushforward
import OAI.AlgebraicGeometry.SheafCohomology.Cech.Comparison
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechAllDegrees

/-! # Acyclic Pushforward Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.AcyclicPushforwardComparison

noncomputable section

/-! Actual cohomology of a direct image and of its source agree when
the inverse images of an affine cover have acyclic intersections. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

open OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechAllDegrees
universe u

def pushforwardCohomologyAcyclicCoverEquiv
    {X Y : Scheme.{u}} [Y.IsSeparated] (f : X ⟶ Y)
    [QuasiCompact f] [IsSeparated f] (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens)
    (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (hacyc : SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (fun i => f ⁻¹ᵁ U i)
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) (n : ℕ) :
    SheafCohomology.AffineH.Projective.H ((pushforward f).obj M) (n + 1) ≃+ SheafCohomology.AffineH.Projective.H M (n + 1) := by
  let W := (pushforward f).obj M
  let V := fun i => f ⁻¹ᵁ U i
  have : W.IsQuasicoherent := QuasicoherentPushforward.quasicoherent_pushforward_of_quasiCompact_separated f M
  letI := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule (𝟙 Y) W (n + 1)
  let eY := SheafCohomology.Projective.BaseCechAllDegrees.orderedBaseCechHomologyAffineHLinearEquiv (𝟙 Y) W U hU hUa (n + 1)
  let eP := HomologicalComplex.homologyMapIso
    (SheafCohomology.Projective.OrderedBaseCechPushforward.Scheme.Modules.orderedBaseCechComplexPushforwardIso f (𝟙 Y) M U) (n + 1)
  let eO := SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomologyIso (f ≫ 𝟙 Y) M V (n + 1)
  let eN := SheafCohomology.Projective.BaseCechHomology.Scheme.Modules.baseCechComplexHomologyForgetIso (f ≫ 𝟙 Y) M V (n + 1)
  let eH := SheafCohomology.Cech.Comparison.TopCat.Sheaf.cechHomologySuccIsoOfAcyclicIntersections V
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
    (hU.comap f.base.hom).iSup_eq_top hacyc n
  exact eY.toAddEquiv.symm.trans (eP.symm.toLinearEquiv.toAddEquiv.trans
    (eO.symm.toLinearEquiv.toAddEquiv.trans
      (eN.addCommGroupIsoToAddEquiv.trans eH.addCommGroupIsoToAddEquiv)))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.AcyclicPushforwardComparison
