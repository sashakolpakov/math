import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardZariskiComparison

/-! # Acyclic Pushforward Cohomology Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AcyclicPushforwardCohomologyComparison

noncomputable section

/-! Direct image cohomology agrees with source cohomology when inverse images of the affine cover have acyclic intersections. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u

def pushforwardCohomologyAcyclicCoverEquiv
    {X Y : Scheme.{u}} [Y.IsSeparated] (f : X ⟶ Y)
    [QuasiCompact f] [IsSeparated f] (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens)
    (hU : ⨆ i, U i = ⊤) (hUa : ∀ i, IsAffineOpen (U i))
    (hacyc : Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic (fun i => f ⁻¹ᵁ U i)
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) (n : ℕ) :
    Zariski.Cohomology.ZariskiCohomology.H ((Scheme.Modules.pushforward f).obj M) (n + 1) ≃+
      Zariski.Cohomology.ZariskiCohomology.H M (n + 1) := by
  let W := (Scheme.Modules.pushforward f).obj M
  let V := fun i => f ⁻¹ᵁ U i
  have : W.IsQuasicoherent := Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent f M
  let c : Γ(Y, ⊤) →+* Γ(Y, ⊤) := RingHom.id _
  let eY := OrderedCech.ZariskiComparison.orderedCechZariskiModuleIso c W U hU hUa n
  let eP := HomologicalComplex.homologyMapIso
    (OrderedCech.PushforwardComplex.orderedCoefficientCechComplexPushforwardIso f c M U) (n + 1)
  let eO := Ordered.CoefficientCechHomotopyEquivalence.coefficientCechOrderedHomologyIso (f.appTop.hom.comp c) M V (n + 1)
  let eN := CoefficientCech.HomologyForget.coefficientCechComplexHomologyForgetIso (f.appTop.hom.comp c) M V (n + 1)
  let eH := IntrinsicCech.SheafCohomologyComparison.cechHomologySuccIsoOfAcyclicIntersections V
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
    (Affine.PushforwardZariskiComparison.inverseImageOpens_iSup_eq_top f U hU) hacyc n
  exact eY.toLinearEquiv.toAddEquiv.symm.trans (eP.symm.toLinearEquiv.toAddEquiv.trans
    (eO.symm.toLinearEquiv.toAddEquiv.trans
      (eN.addCommGroupIsoToAddEquiv.trans eH.addCommGroupIsoToAddEquiv)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AcyclicPushforwardCohomologyComparison
