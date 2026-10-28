import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AlbaneseProjectivity
import OAI.RepresentationTheory.Theta.Geometric.Data

/-! # Albanese -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Albanese

noncomputable section

/-! IntegralModel's actual group geometry constructs the projective Albanese
presentation required by FrobeniusSlope. No replacement abelian variety or
projective-presentation hypothesis is supplied. -/

open OAI.RepresentationTheory.Theta.Geometric.Data

def nativeAlbaneseProjectiveOfGeometry
    {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) :
    Foundations.Scheme.SmoothProjective.ProjectivePresentation D.pel.complexAlbanese.X.left D.pel.complexAlbanese.X.hom :=
  (D.pel.actualComplexAlbaneseVariety hg).variety.presentation.projective

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Albanese
