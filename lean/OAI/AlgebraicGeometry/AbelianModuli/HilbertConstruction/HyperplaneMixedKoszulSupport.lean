import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HyperplaneTorsionFiniteCuts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MixedKoszulGeometricSupport

/-! # Hyperplane Mixed Koszul Support -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HyperplaneMixedKoszulSupport

noncomputable section

/-! The finite intersection constructed by hyperplanes is the actual
common zero set of the mixed Koszul complex formed from one original
section and the pulled-back sections. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}}

def hyperplanePullbackSections (L : Line.Bundles.LineBundle X) (a : Line.Bundles.structureModule X ⟶ L.sheaf)
    (m : X ⟶ X) (ts : List (Line.Bundles.structureModule X ⟶ L.sheaf)) : List (LineBundleKoszulComplex.LineBundleSection X) :=
  ⟨L, a⟩ :: ts.map (fun t => ⟨L.pullback m, Ample.LineBundles.pullbackSection m t⟩)

theorem hyperplanePullbackSections_length (L : Line.Bundles.LineBundle X) (a : Line.Bundles.structureModule X ⟶ L.sheaf)
    (m : X ⟶ X) (ts : List (Line.Bundles.structureModule X ⟶ L.sheaf)) :
    (hyperplanePullbackSections L a m ts).length = ts.length + 1 := by
  simp only [hyperplanePullbackSections, List.length_cons, List.length_map]

theorem hyperplanePullbackSections_zeroSet (L : Line.Bundles.LineBundle X) (a : Line.Bundles.structureModule X ⟶ L.sheaf)
    (m : X ⟶ X) (ts : List (Line.Bundles.structureModule X ⟶ L.sheaf)) :
    MixedKoszulGeometricSupport.mixedSectionZeroSet (hyperplanePullbackSections L a m ts) =
      {x : X | x ∉ Ample.LineBundles.sectionNonvanishing a ∧ ∀ t ∈ ts, m x ∉ Ample.LineBundles.sectionNonvanishing t} := by
  ext x
  change (∀ b ∈ hyperplanePullbackSections L a m ts, x ∉ Ample.LineBundles.sectionNonvanishing b.2) ↔ _
  simp only [hyperplanePullbackSections, List.forall_mem_cons, List.forall_mem_map]
  simp only [LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange]
  rfl

theorem exists_hyperplane_mixedKoszul_finite_support
    {K : Type u} [Field K] [Infinite K] [NoetherianSpace X] [IrreducibleSpace X]
    (p : X ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X) {n : ℕ}
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hcover : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ha : ∀ i, IsAffineOpen (Ample.LineBundles.sectionNonvanishing (s i)))
    (hgen : Section.ProjectivePresentation.SectionRatiosGenerate p s)
    (z : Spec (.of K) ⟶ X) (hz : z ≫ p = 𝟙 _)
    (m : X ⟶ X) [LocallyQuasiFinite m]
    (g : ℕ) (hdim : topologicalKrullDim X ≤ (g + 1 : ℕ))
    (a : Line.Bundles.structureModule X ⟶ L.sheaf) (ha_nonzero : ∃ x, x ∈ Ample.LineBundles.sectionNonvanishing a) :
    ∃ ts : List (Line.Bundles.structureModule X ⟶ L.sheaf),
      ts.length = g ∧
      (∀ t ∈ ts, z (IsLocalRing.closedPoint K) ∉ Ample.LineBundles.sectionNonvanishing t) ∧
      (MixedKoszulGeometricSupport.mixedSectionZeroSet (hyperplanePullbackSections L a m ts)).Finite := by
  obtain ⟨ts, hlen, hzts, hf⟩ := HyperplaneTorsionFiniteCuts.exists_hyperplane_cuts_with_finite_support
    p L s hcover ha hgen z hz m g hdim a ha_nonzero
  refine ⟨ts, hlen, hzts, ?_⟩
  rwa [hyperplanePullbackSections_zeroSet]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HyperplaneMixedKoszulSupport
