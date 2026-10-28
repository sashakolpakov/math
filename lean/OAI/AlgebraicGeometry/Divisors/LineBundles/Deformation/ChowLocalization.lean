import OAI.AlgebraicGeometry.Divisors.LineBundles.ChowLocalization
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.ConeFiniteType
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.Specialization

/-! # Chow Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.ChowLocalization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: Chow localization on the constructed global deformation

The nonvanishing locus of the actual global parameter is the complement
of the proved closed normal-cone fiber. The genuine Chow localization
sequence therefore applies to this deformation, with no relation or
intersection-theory compatibility assumed.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme} (I : X.IdealSheafData)

/-- The actual open locus where the deformation parameter is invertible. -/
def globalDeformationPuncturedOpen : (Global.Deformation.BundleCycles.globalDeformation I).Opens :=
  (Global.Deformation.BundleCycles.globalDeformation I).basicOpen (Global.Specialization.BundleCycles.globalDeformationParameterSection I)

def globalDeformationPunctured : Scheme := (globalDeformationPuncturedOpen I).toScheme

def globalDeformationPuncturedInclusion : globalDeformationPunctured I ⟶ Global.Deformation.BundleCycles.globalDeformation I :=
  (globalDeformationPuncturedOpen I).ι

instance globalDeformationPuncturedInclusion_isOpenImmersion :
    IsOpenImmersion (globalDeformationPuncturedInclusion I) :=
  inferInstanceAs (IsOpenImmersion (globalDeformationPuncturedOpen I).ι)

/-- The actual normal-cone fiber is exactly the closed complement of the punctured deformation. -/
theorem globalDeformationPunctured_closed_complement :
    Set.range (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I) = (Set.range (globalDeformationPuncturedInclusion I))ᶜ :=
  (Global.Specialization.BundleCycles.globalSpecialFiberMap_range I).trans
    (congrArg (fun s : Set (Global.Deformation.BundleCycles.globalDeformation I) => sᶜ) (globalDeformationPuncturedOpen I).range_ι.symm)

variable [AlgebraicGeometry.IsNoetherian X]

instance globalDeformationPunctured_isNoetherian : AlgebraicGeometry.IsNoetherian (globalDeformationPunctured I) := by
  have : IsLocallyNoetherian (globalDeformationPunctured I) :=
    LocallyOfFiniteType.isLocallyNoetherian (globalDeformationPuncturedInclusion I)
  have : NoetherianSpace (globalDeformationPunctured I) :=
    (globalDeformationPuncturedInclusion I).isOpenEmbedding.isInducing.noetherianSpace
  exact ⟨⟩

variable (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

/-- Chow restriction from the actual deformation to its punctured open. -/
def deformationChowRestriction (d : ℕ) :
    DimensionChow.BundleCycles.DimensionChowQ (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f) d →ₗ[ℚ]
      DimensionChow.BundleCycles.DimensionChowQ (globalDeformationPuncturedInclusion I ≫ (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f)) d :=
  Open.ChowRestriction.BundleCycles.openChowRestriction (globalDeformationPuncturedInclusion I) (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f) d

/-- Closed-fiber Chow pushforward along the actual normal-cone inclusion. -/
def deformationChowFiberPushforward (d : ℕ) :
    DimensionChow.BundleCycles.DimensionChowQ (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I ≫ (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f)) d →ₗ[ℚ]
      DimensionChow.BundleCycles.DimensionChowQ (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f) d :=
  Closed.ChowPushforward.BundleCycles.closedChowPushforward (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I) (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f) d

theorem deformationChowRestriction_surjective (d : ℕ) :
    Function.Surjective (deformationChowRestriction I f d) :=
  Open.ChowRestriction.BundleCycles.openChowRestriction_surjective (globalDeformationPuncturedInclusion I) (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f) d

/-- Exact Chow localization for the constructed deformation and its actual closed fiber. -/
theorem deformationChowLocalization_exact (d : ℕ) :
    LinearMap.range (deformationChowFiberPushforward I f d) = LinearMap.ker (deformationChowRestriction I f d) :=
  ChowLocalization.BundleCycles.chowLocalization_exact (globalDeformationPuncturedInclusion I) (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I)
    (globalDeformationPunctured_closed_complement I) (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f) d

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.ChowLocalization.BundleCycles
