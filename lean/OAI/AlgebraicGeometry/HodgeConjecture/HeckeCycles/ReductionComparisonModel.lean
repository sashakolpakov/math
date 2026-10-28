import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeSquare

/-! # Reduction Comparison Model -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionComparisonModel.CM

noncomputable section

/-! Construct both source and abelian target identifications for a
commuting reduction square, together with the proved map compatibility. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeSquare.CM

variable {S T U : Scheme} {g : ℕ} (G : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {X : Over S} (a : X ⟶ G.scheme) (r : U ⟶ T) (t : T ⟶ S) (b : U ⟶ S)

structure ReductionMap where
  sourceIso : (Over.pullback r).obj ((Over.pullback t).obj X) ≅ (Over.pullback b).obj X
  targetIso : ((G.pullback t).pullback r).scheme ≅ (G.pullback b).scheme
  target_group : IsMonHom targetIso.hom
  compatible :
    (Over.pullback r).map ((Over.pullback t).map a) ≫ targetIso.hom =
      sourceIso.hom ≫ (Over.pullback b).map a

def reductionMap (w : r ≫ t = b) : ReductionMap G a r t b where
  sourceIso := (BaseChangeSquare.CM.factorIso r t b w X).symm
  targetIso := (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso G r t b w).symm
  target_group := (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorGroupIso G r t b w).inv.hom.isMonHom_hom
  compatible := by
    have he : AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso G r t b w = BaseChangeSquare.CM.factorIso r t b w G.scheme :=
      Iso.ext (BaseChangeSquare.CM.groupFactor_hom r t b w G)
    exact (congrArg ((Over.pullback r).map ((Over.pullback t).map a) ≫ ·)
      (congrArg Iso.inv he)).trans (BaseChangeSquare.CM.factorIso_inv_naturality r t b w a)

theorem reductionMap_target_hom (w : r ≫ t = b) :
    (reductionMap G a r t b w).targetIso.hom = (BaseChangeSquare.CM.factorIso r t b w G.scheme).inv := by
  have he : AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso G r t b w = BaseChangeSquare.CM.factorIso r t b w G.scheme :=
    Iso.ext (BaseChangeSquare.CM.groupFactor_hom r t b w G)
  exact congrArg Iso.inv he

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionComparisonModel.CM
