import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TorsionLine
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullback
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionBase
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ReducedClosedIs
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Torsion Section -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.TorsionSection.Construction.TorsionSectionFinite

noncomputable section

/-! Finiteness from affine nonvanishing loci of torsion line bundles.
The line bundle may vary with the point; no single ample bundle is required. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem affine_of_section {K : Type u} [Field K]
    (X : Over (Spec (.of K))) [IsProper X.hom] [ConnectedSpace X.left] [IsReduced X.left]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (n : ℕ) (hn : 0 < n)
    (e : (L.tensorPower n).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left ⟶ L.sheaf)
    (hs : (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s : Set X.left).Nonempty)
    (ha : IsAffineOpen (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s)) : IsAffine X.left := by
  have : IsIso s := TorsionLine.Construction.TorsionLineBundle.isIso_of_nonempty_nonvanishing X L n hn e s hs
  rw [AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing_of_isIso] at ha
  have : IsAffine (⊤ : X.left.Opens).toScheme := ha
  exact IsAffine.of_isIso X.left.topIso.inv

/-- On a proper scheme over a field, an affine neighborhood at every point
cut out by a section of a torsion line bundle forces finiteness. -/
theorem isFinite {K : Type u} [Field K]
    (X : Over (Spec (.of K))) [IsProper X.hom]
    (h : ∀ x : X.left, ∃ (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (n : ℕ), 0 < n ∧
      Nonempty ((L.tensorPower n).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left) ∧
      ∃ s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left ⟶ L.sheaf,
        x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s ∧ IsAffineOpen (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s)) : IsFinite X.hom := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  have hc (Z : Set X.left) (hZ : Z ∈ irreducibleComponents X.left) : Z.Finite := by
    let C : TopologicalSpace.Closeds X.left := ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩
    let I := Scheme.IdealSheafData.vanishingIdeal C
    let T : Over (Spec (.of K)) := Over.mk (I.subschemeι ≫ X.hom)
    have : IsProper T.hom := by dsimp [T]; infer_instance
    have : IsReduced T.left := ReducedClosedIs.Construction.ReducedClosed.isReduced C
    have : IrreducibleSpace T.left := ReducedClosedIs.Construction.ReducedClosed.irreducibleSpace C hZ.1
    let x : T.left := Classical.choice (inferInstance : Nonempty T.left)
    obtain ⟨L, n, hn, ⟨e⟩, s, hx, ha⟩ := h (I.subschemeι x)
    let eT : ((L.pullback I.subschemeι).tensorPower n).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left :=
      (TensorPullback.Construction.TensorPullbackMap.iso I.subschemeι L n).symm ≪≫
        (Scheme.Modules.pullback I.subschemeι).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso I.subschemeι
    let t := AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection I.subschemeι s
    have ht : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t = I.subschemeι ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s :=
      SectionBase.Construction.SectionBaseChange.nonvanishing_pullback I.subschemeι L s
    have hta : IsAffineOpen (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t) := ht.symm ▸ ha.preimage I.subschemeι
    have htx : x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t := ht.symm ▸ hx
    have : IsAffine T.left := affine_of_section T (L.pullback I.subschemeι) n hn eT t ⟨x, htx⟩ hta
    have : IsFinite T.hom := ProperFunctionsEq.Construction.ProperFunctions.finite_of_proper_affine T.hom
    have : IsLocallyArtinian T.left := IsLocallyArtinian.of_locallyQuasiFinite T.hom
    have : Subsingleton T.left := subsingleton_of_preconnected_totallyDisconnected
    have : Finite I.subscheme := inferInstanceAs (Finite T.left)
    have hr : Set.range I.subschemeι = Z := ReducedClosedIs.Construction.ReducedClosed.range_ι C
    rw [← hr]
    exact Set.finite_range I.subschemeι
  have hu : (⋃₀ irreducibleComponents X.left).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sUnion hc
  rw [sUnion_irreducibleComponents] at hu
  have : Finite X.left := Set.finite_univ_iff.mp hu
  have : LocallyQuasiFinite X.hom :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (fun _ => Set.toFinite _)
  exact IsFinite.of_isProper_of_locallyQuasiFinite X.hom

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.TorsionSection.Construction.TorsionSectionFinite
