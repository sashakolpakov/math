import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Space
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.ChartProperties

/-! # Space Properties -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.SpaceProperties.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: Noetherianity of finite relative affine spaces -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (ι : Type) [Finite ι] (X : Scheme.{0})

instance finiteAffineSpace_isLocallyNoetherian [IsLocallyNoetherian X] :
    IsLocallyNoetherian (AffineSpace ι X) :=
  LocallyOfFiniteType.isLocallyNoetherian (AffineSpace ι X ↘ X)

instance finiteAffineSpace_isNoetherian [AlgebraicGeometry.IsNoetherian X] :
    AlgebraicGeometry.IsNoetherian (AffineSpace ι X) := by
  have : CompactSpace (AffineSpace ι X) :=
    QuasiCompact.compactSpace_of_compactSpace (AffineSpace ι X ↘ X)
  exact ⟨⟩

end

/-! # LineBundleCycles: smoothness and integrality of actual finite relative affine spaces -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (ι : Type) [Finite ι] (X : Scheme.{0})

instance finiteAffineSpaceProjection_smooth : Smooth (AffineSpace ι X ↘ X) := by
  have : IsZariskiLocalAtTarget (@Smooth.{0}) := HasRingHomProperty.instIsZariskiLocalAtTarget _
  apply Global.DeformationProperties.BundleCycles.morphismProperty_of_cover_pullbacks (@Smooth) (AffineSpace ι X ↘ X) X.affineCover
    (fun i => AffineSpace ι (X.affineCover.X i))
    (fun i => AffineSpace.map ι (X.affineCover.f i))
    (fun i => AffineSpace ι (X.affineCover.X i) ↘ X.affineCover.X i)
    (fun i => (AffineSpace.isPullback_map (n := ι) (X.affineCover.f i)).flip)
  intro i
  exact LineBundles.AffineSpace.ChartProperties.BundleCycles.affineSpaceSpecProjection_smooth _ ι

instance finiteAffineSpace_isIntegral [IsIntegral X] [IsLocallyNoetherian X] :
    IsIntegral (AffineSpace ι X) :=
  GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (AffineSpace ι X ↘ X)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.SpaceProperties.BundleCycles
