import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionComparisonModel

/-! # Reduction Target Identification -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionTargetIdentification.CM

noncomputable section

/-! Replace a reduction square's target comparison by a proved equal
isomorphism. This retains its source map and proved commuting square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionComparisonModel.CM

variable {S T U : Scheme} {g : ℕ} (G : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {X : Over S} (a : X ⟶ G.scheme) (r : U ⟶ T) (t : T ⟶ S) (b : U ⟶ S)
  (M : ReductionComparisonModel.CM.ReductionMap G a r t b)
  (e : ((G.pullback t).pullback r).scheme ≅ (G.pullback b).scheme)
  (he : M.targetIso.hom = e.hom)

def replaceTarget : ReductionComparisonModel.CM.ReductionMap G a r t b where
  sourceIso := M.sourceIso
  targetIso := e
  target_group := he ▸ M.target_group
  compatible :=
    (congrArg ((Over.pullback r).map ((Over.pullback t).map a) ≫ ·) he.symm).trans M.compatible

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionTargetIdentification.CM
