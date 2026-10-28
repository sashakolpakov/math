import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ProjectiveGlobalGeneration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.TwistingSectionsFinite
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.ProjectiveEmbeddings
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.Powers

/-! # Global Generation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A constructed positive-power projective embedding yields finite global generators for every coherent sheaf after all sufficiently positive twists along that degree. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem PowerEmbedding.GlobalGeneration.relativeEmbedding_tensorTwistingPowers_eventually_hasFiniteGlobalGenerators
    {R : Type u} [CommRing R] {n : ℕ} {X : Over (Spec (.of R))}
    (i : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of R)) n) [IsClosedImmersion i.left]
    (M : X.left.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d → Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators
      (Tensor.ProductSheaf.tensorModule M (((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of R)) n).pullback i.left).tensorPower d).sheaf) := by
  obtain ⟨B, hB⟩ := Closed.ProjectiveGlobalGeneration.ClosedProjectiveEmbedding.tensorTwistingPowers_eventually_hasFiniteGlobalGenerators
    (RelativeProjective.TwistingSectionsFinite.relativeEmbeddingAffineMap i) M
  refine ⟨B, fun d hd => ?_⟩
  let E := Tensor.ProductSheaf.tensorModuleCongr (Iso.refl M)
    ((TensorPower.Maps.tensorPowerFunctor X.left d).mapIso (RelativeProjective.TwistingSectionsFinite.relativeEmbeddingAffineTwistingIso i))
  exact (hB d hd).of_iso E

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.tensorPowers_eventually_hasFiniteGlobalGenerators
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}
    {L : Line.Bundles.LineBundle X} (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L f)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ B : ℕ, ∀ m : ℕ, B ≤ m →
      Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators (Tensor.ProductSheaf.tensorModule M (L.tensorPower (m * E.degree)).sheaf) := by
  let i := SectionsProjectiveMorphism.sectionProjectiveMorphism f E.sections E.covers
  have : IsClosedImmersion i.left := E.closedImmersion
  obtain ⟨B, hB⟩ := PowerEmbedding.GlobalGeneration.relativeEmbedding_tensorTwistingPowers_eventually_hasFiniteGlobalGenerators i M
  let eP := (E.isPower.unique (L.tensorPower_isTensorPower E.degree)).some
  refine ⟨B, fun m hm => ?_⟩
  let eT := (TensorPower.Maps.tensorPowerFunctor X m).mapIso (E.twistingBundleIso f ≪≫ eP) ≪≫
    (L.tensorPowerComposeIso m E.degree).symm
  exact (hB m hm).of_iso (Tensor.ProductSheaf.tensorModuleCongr (Iso.refl M) eT)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
