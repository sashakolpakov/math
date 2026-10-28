import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.CommonCoverCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.DegreeZeroIsomorphism

/-! # Common Cover Degree Zero -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.CommonCoverDegreeZero

noncomputable section

/-! The common-cover cohomology comparison in degree zero uses actual global sections and the native Ext degree-zero equivalence. No acyclicity hypothesis is needed in degree zero. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
universe u

def additiveCommonCoverZeroCohomologyIso
    {X P : Scheme.{u}} (a : P ⟶ X) {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (F : P.carrier.Sheaf AddCommGrpCat.{u}) :
    ((cechComplexFunctor U).obj ((Opens.map a.base).op ⋙ F.obj)).homology 0 ≅
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology P) 0).obj F := by
  let F' : CategoryTheory.Sheaf (Opens.grothendieckTopology P.carrier) AddCommGrpCat.{u} := F
  let H : AddCommGrpCat.{u} := (CategoryTheory.Sheaf.functorH
    (Opens.grothendieckTopology P.carrier) 0).obj F'
  let e : H ≃+ F'.obj.obj (op ⊤) :=
    CategoryTheory.Sheaf.H.equiv₀ F' (isTerminalTop : IsTerminal (⊤ : Opens P.carrier))
  exact (HomologicalComplex.homologyMapIso (CechPushforward.additiveCechPushforwardComplexIso a F.obj U) 0).symm ≪≫
    (IntrinsicCech.DegreeZeroIsomorphism.cechTopSectionsHZeroIso (fun i => a ⁻¹ᵁ U i) F
      (Affine.PushforwardZariskiComparison.inverseImageOpens_iSup_eq_top a U hU)).symm ≪≫
    e.symm.toAddCommGrpIso

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.CommonCoverDegreeZero
