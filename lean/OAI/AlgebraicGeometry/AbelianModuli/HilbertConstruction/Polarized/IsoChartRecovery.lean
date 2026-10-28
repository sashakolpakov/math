import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.IsoOpenChart
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.IsoMorphismProperty

/-! # Iso Chart Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized

noncomputable section

/-! Any scheme representing the complete isomorphism functor recovers the constructed quasi-projective parameter on each base chart. Its local finite-type and quasi-compact properties follow from this actual isomorphism. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable {A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S} {x : S}
variable (C : IsoOpenChart.PolarizedIsoOpenChart A B x) (M : Over S)
variable (e : Family.LevelIsoFunctor.familyLevelIsoFunctor A B ≅ yoneda.obj M)

def IsoOpenChart.PolarizedIsoOpenChart.pullbackParameterIso : (Over.pullback C.inclusion).obj M ≅ C.parameter :=
  yoneda.preimageIso (((Over.mapPullbackAdj C.inclusion).compYonedaIso.app M) ≪≫
    (Functor.isoWhiskerLeft (Over.map C.inclusion).op e).symm ≪≫ C.representation)

include e in
theorem IsoOpenChart.PolarizedIsoOpenChart.pullback_locallyOfFiniteType : LocallyOfFiniteType ((Over.pullback C.inclusion).obj M).hom :=
  (HilbertConstruction.Over.IsoMorphismProperty.overIso_morphismProperty_iff (@LocallyOfFiniteType) (C.pullbackParameterIso M e)).mpr
    C.quasiProjective.some.locallyFiniteType

include e in
theorem IsoOpenChart.PolarizedIsoOpenChart.pullback_quasiCompact : QuasiCompact ((Over.pullback C.inclusion).obj M).hom :=
  (HilbertConstruction.Over.IsoMorphismProperty.overIso_morphismProperty_iff (@QuasiCompact) (C.pullbackParameterIso M e)).mpr
    C.quasiProjective.some.quasiCompact

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized
