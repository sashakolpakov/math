import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.BundleIsoDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsoIdentityBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.BaseChangedSectionConstants
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.PolarizationGraphPower
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PolarizationEnhancementData

/-! # Graph Power Iso Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GraphPowerIsoDescent

noncomputable section

/-! Once the original dual and polarization have descended, the graph-power
isomorphism descends from a Zariski cover on every test of a fixed projective
family. An actual trivialization at zero is required and retained. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
universe u

variable {S T : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (t : T ⟶ S)
    (level : (A.pullback t).FullLevel N) (D : Dual.Data.DualAbelianData (A.pullback t))
    (pol : PolarizationData.Polarization D δ)

def normalizedGraphPowerTarget : PolarizationData.PolarizedAbelianWithFullLevel g δ N T :=
  ⟨A.pullback t, D, pol, level⟩

include P in
/-- The chosen zero fibers remove the possible line-bundle twist from the base. -/
theorem normalizedGraphPowerIso_of_cover
    (L : Line.Bundles.LineBundle (A.pullback t).scheme.left)
    (zero : (L.pullback η[(A.pullback t).scheme].left).sheaf ≅ Line.Bundles.structureModule T)
    (d : ℕ) (R : Sieve (Over.mk (𝟙 T)))
    (hR : R ∈ (Scheme.zariskiTopology.over T) (Over.mk (𝟙 T)))
    (hlocal : ∀ {U : Over T} (f : U ⟶ Over.mk (𝟙 T)), R f →
      Nonempty ((Relative.BundleIsoSheaf.relativeBundleIsoPresheaf (A.pullback t).scheme.hom L
        ((normalizedGraphPowerTarget A t level D pol).graphBundle.tensorPower d)).obj (.op U))) :
    Nonempty (L.sheaf ≅ ((normalizedGraphPowerTarget A t level D pol).graphBundle.tensorPower d).sheaf) := by
  let B := normalizedGraphPowerTarget A t level D pol
  let G := B.graphBundle.tensorPower d
  let zG : (G.pullback η[(A.pullback t).scheme].left).sheaf ≅ Line.Bundles.structureModule T :=
    Classical.choice (Quotient.exact (B.graphBundlePower_zero_class d))
  let b : (Scheme.Modules.pullback η[(A.pullback t).scheme].left).obj L.sheaf ≅
      (Scheme.Modules.pullback η[(A.pullback t).scheme].left).obj G.sheaf := zero ≪≫ zG.symm
  apply (IsoIdentityBaseChange.relativeBundleIso_identity_nonempty_iff (A.pullback t).scheme.hom L G).mp
  exact BundleIsoDescent.relativeBundleIso_nonempty_of_cover (A.pullback t).scheme.hom
    η[(A.pullback t).scheme].left η[(A.pullback t).scheme].w L G b Scheme.zariskiTopology
    (Projective.BaseChangedSectionConstants.projectivePresentation_iteratedBaseChangeSection_bijective P
      η[A.scheme].left η[A.scheme].w (IsPullback.of_hasPullback A.scheme.hom t)
      η[(A.pullback t).scheme].left η[(A.pullback t).scheme].w)
    (Over.mk (𝟙 T)) R hR hlocal

include P in
/-- The actual zero-normalized input used by the rational polarization locus
has the required global zero frame after every base change. -/
theorem zeroNormalizedGraphPowerIso_of_cover
    (L : Line.Bundles.LineBundle A.scheme.left) (d : ℕ) (R : Sieve (Over.mk (𝟙 T)))
    (hR : R ∈ (Scheme.zariskiTopology.over T) (Over.mk (𝟙 T)))
    (hlocal : ∀ {U : Over T} (f : U ⟶ Over.mk (𝟙 T)), R f →
      Nonempty ((Relative.BundleIsoSheaf.relativeBundleIsoPresheaf (A.pullback t).scheme.hom
        ((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom t))
        ((normalizedGraphPowerTarget A t level D pol).graphBundle.tensorPower d)).obj (.op U))) :
    Nonempty (((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom t)).sheaf ≅
      ((normalizedGraphPowerTarget A t level D pol).graphBundle.tensorPower d).sheaf) := by
  let zero :=
    (Scheme.Modules.pullback η[(A.pullback t).scheme].left).mapIso
      (A.zeroNormalizedBundle_baseChangeIso L t) ≪≫
      (A.pullback t).zeroNormalizedBundle_zeroIso (L.pullback (pullback.fst A.scheme.hom t))
  exact normalizedGraphPowerIso_of_cover A P t level D pol _ zero d R hR hlocal

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GraphPowerIsoDescent
