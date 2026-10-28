import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TorsionSectionDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.SectionPullbackComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsomorphismSectionVanishing

/-! # Detection By Families -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Detection by a family means that actual pullbacks of a section
vanish only when that section is zero. It is preserved by isomorphisms
of schemes and line bundles. High torsion supplies this property. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped Classical
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y S : Scheme.{u}} {ι : Type v}

def Section.DetectionByFamilies.SectionsDetectedBy (L : Line.Bundles.LineBundle X) (x : ι → (S ⟶ X)) : Prop :=
  ∀ a : Line.Bundles.structureModule X ⟶ L.sheaf, (∀ i, Ample.LineBundles.pullbackSection (x i) a = 0) → a = 0

theorem Section.DetectionByFamilies.pullbackSection_comp_eq_zero_iff (x : S ⟶ X) (f : X ⟶ Y)
    {M : Y.Modules} (a : Line.Bundles.structureModule Y ⟶ M) :
    Ample.LineBundles.pullbackSection (x ≫ f) a = 0 ↔ Ample.LineBundles.pullbackSection x (Ample.LineBundles.pullbackSection f a) = 0 := by
  constructor
  · intro h
    apply (cancel_mono ((Scheme.Modules.pullbackComp x f).hom.app M)).mp
    rw [Global.SectionPullbackComposition.pullbackSection_composition, h, zero_comp]
  · intro h
    rw [← Global.SectionPullbackComposition.pullbackSection_composition x f a, h, zero_comp]

theorem Section.DetectionByFamilies.SectionsDetectedBy.of_schemeIso {L : Line.Bundles.LineBundle Y} {M : Line.Bundles.LineBundle X}
    (x : ι → (S ⟶ X)) (h : Section.DetectionByFamilies.SectionsDetectedBy M x) (e : X ≅ Y)
    (H : (L.pullback e.hom).sheaf ≅ M.sheaf) :
    Section.DetectionByFamilies.SectionsDetectedBy L (fun i => x i ≫ e.hom) := by
  intro a ha
  have hz : Ample.LineBundles.pullbackSection e.hom a ≫ H.hom = 0 := by
    apply h
    intro i
    rw [Power.SectionTransitions.pullbackSection_postcomp,
      (Section.DetectionByFamilies.pullbackSection_comp_eq_zero_iff (x i) e.hom a).mp (ha i), zero_comp]
  have hp : Ample.LineBundles.pullbackSection e.hom a = 0 := by
    apply (cancel_mono H.hom).mp
    simpa only [zero_comp] using hz
  exact (IsomorphismSectionVanishing.pullbackSection_iso_eq_zero_iff e.hom a).mp hp

variable {R : Type u} [CommRing R] {g N n r : ℕ} {δ : Fin g → ℕ} [NeZero n]
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.evenGraphPower_sectionsDetectedBy_fullLevel
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N)
    (hunit : IsUnit (N : Γ(Spec (.of R), ⊤)))
    (level : A.abelian.FullLevel n) (t : ℕ) (ht : 0 < t)
    (htlarge : Graph.EmbeddingNumerics.graphSquareSectionRank g δ ≤ t)
    (hlarge : EvenGraphTorsionBound.evenGraphTorsionDegree g δ t < n ^ 2)
    (b : Module.Basis (Fin r) R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj
      (A.graphBundle.tensorPower (2 * t)).sheaf))
    (hs : ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily A.abelian.scheme.hom
      (A.graphBundle.tensorPower (2 * t)).sheaf
      (Coefficient.RingSectionBasis.coefficientRingBasisFamily (Coefficient.ModulePresheaf.schemeCoefficientMap A.abelian.scheme.hom)
        (A.graphBundle.tensorPower (2 * t)).sheaf b) (𝟙 (Spec (.of R))))
    (e : ∀ c : Multiplicative (Fin (2 * g) → ZMod n),
      ((A.graphBundle.tensorPower (2 * t)).pullback (A.abelian.fullLevelGlobalSection level c)).sheaf ≅
        Line.Bundles.structureModule (Spec (.of R))) :
    Section.DetectionByFamilies.SectionsDetectedBy (A.graphBundle.tensorPower (2 * t)) (A.abelian.fullLevelGlobalSection level) := by
  intro a ha
  apply A.affineEvenGraphPower_section_eq_zero_of_framed_values hg hδ hN hunit
    level t ht htlarge hlarge b hs e a
  intro c
  simp only [Affine.FramedSectionEvaluation.affineFramedSectionValue, Family.FramedSectionEvaluation.familyFramedSectionValue, ha c, zero_comp, map_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
