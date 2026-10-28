import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationSectionData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.GraphBundles

/-! # Source Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! An isomorphism of the source and defining line bundle transports the
actual power embedding while preserving its degree and projective dimension. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
section
variable {S : Scheme.{u}} {X Y : Over S} {L : Line.Bundles.LineBundle Y.left} {M : Line.Bundles.LineBundle X.left}

def Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.ofSourceIso (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L Y.hom) (e : X ≅ Y)
    (eL : (L.pullback e.hom.left).sheaf ≅ M.sheaf) : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding M X.hom where
  degree := E.degree
  degree_pos := E.degree_pos
  power := E.power.pullback e.hom.left
  isPower := (M.tensorPower_isTensorPower E.degree).of_targetIso
    (((Scheme.Modules.pullback e.hom.left).mapIso
      (E.isPower.unique (L.tensorPower_isTensorPower E.degree)).some ≪≫
        L.powerBaseChangeIso e.hom.left E.degree ≪≫
          (TensorPower.Maps.tensorPowerFunctor X.left E.degree).mapIso eL).symm)
  dimension := E.dimension
  sections i := Ample.LineBundles.pullbackSection e.hom.left (E.sections i)
  covers := Section.ChartArbitraryPullback.lineBundleSections_pullback_covers e.hom.left E.power E.sections E.covers
  closedImmersion := by
    let j := SectionsProjectiveMorphism.sectionProjectiveMorphism Y.hom E.sections E.covers
    have hc : IsClosedImmersion (e.hom ≫ j).left :=
      @IsClosedImmersion.comp _ _ _ _ _ (Grassmann.ProjectivePresentation.overIso_closedImmersion e) E.closedImmersion
    have h := Section.ProjectivePrecomposition.sectionProjectiveMorphism_precomp e.hom E.power E.sections E.covers
      (Section.ChartArbitraryPullback.lineBundleSections_pullback_covers e.hom.left E.power E.sections E.covers)
    exact (congrArg (fun a => IsClosedImmersion a.left) h).mp hc

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.ofSourceIso_degree (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L Y.hom) (e : X ≅ Y)
    (eL : (L.pullback e.hom.left).sheaf ≅ M.sheaf) : (E.ofSourceIso e eL).degree = E.degree := rfl

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.ofSourceIso_dimension (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L Y.hom) (e : X ≅ Y)
    (eL : (L.pullback e.hom.left).sheaf ≅ M.sheaf) : (E.ofSourceIso e eL).dimension = E.dimension := rfl
end

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable {A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S}

def Moduli.Isomorphisms.LevelPreservingIso.graphPowerEmbedding (e : Moduli.Isomorphisms.LevelPreservingIso A B)
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding B.graphBundle B.abelian.scheme.hom) :
    Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom :=
  E.ofSourceIso e.abelian e.graphBundleIso

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
