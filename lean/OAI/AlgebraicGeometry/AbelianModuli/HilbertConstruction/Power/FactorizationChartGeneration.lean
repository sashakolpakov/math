import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionCoordinateSubring
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Canonical.UnaryTensorPower
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.SectionExtension

/-! # Factorization Chart Generation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.FactorizationChartGeneration

noncomputable section

/-! On a quasi-compact separated scheme, positive-power section extension
turns consecutive section factorizations into generation of each chart ring
by ordinary section ratios. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] SectionCoordinateSubring.powerSectionFrame
variable {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]

theorem sectionRatio_subring_eq_top_of_power_factorizations
    (L : Line.Bundles.LineBundle X) (s : Line.Bundles.structureModule X ⟶ L.sheaf)
    (C : Subring Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤))
    (hbase : ∀ t : Line.Bundles.structureModule X ⟶ L.sheaf, Section.Frames.sectionRatio s t ∈ C)
    (hfactor : ∀ m : ℕ, 0 < m → Section.FactorizationSpans.SectionFactorizationSpan (Line.Bundles.structureModule X)
      (L.tensorPower m).sheaf (L.tensorPower (1 + m)).sheaf) : C = ⊤ := by
  apply top_unique
  intro r _
  let U := Ample.LineBundles.sectionNonvanishing s
  have hfirst : ∀ t : Line.Bundles.structureModule X ⟶ (L.tensorPower 1).sheaf,
      SectionCoordinateSubring.sectionPowerCoordinateAddHom L U s 1 t ∈ C := by
    intro t
    let e := Canonical.UnaryTensorPower.canonicalUnaryTensorPowerIso L.sheaf
    have he := SectionTransitions.frameCoordinate_pullback_postcomp U.ι (TensorPower.Maps.tensorPowerSection s 1) s e.hom
      (Canonical.UnaryTensorPower.canonicalUnaryTensorPowerIso_section L.sheaf s) t
    have h := hbase (t ≫ e.hom)
    rw [Frame.Coordinates.sectionRatio_eq_frameCoordinate, he] at h
    exact h
  obtain ⟨n, hn, a, ha⟩ := L.section_extension s r
  have h := SectionCoordinateSubring.sectionPowerCoordinates_mem_of_factorization L U s C hfirst hfactor n hn a
  change Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection U.ι (TensorPower.Maps.tensorPowerSection s n))
    (Ample.LineBundles.pullbackSection U.ι a) ∈ C at h
  change Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection U.ι (TensorPower.Maps.tensorPowerSection s n))
    (Ample.LineBundles.pullbackSection U.ι a) = r at ha
  exact ha ▸ h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.FactorizationChartGeneration
