import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TraceSquareComposition
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LocalNormRefinement
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormRankBasis

/-! # Local Trace Sections -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LocalTraceSections.Construction

noncomputable section

/-! Trace charts allow the finite-flat degree to vary. Their actual
line sections agree on every smaller affine chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u
variable {X Y : Scheme.{u}} (q : X ⟶ Y) [IsFinite q] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)

abbrev TraceFrameOpen := Σ d : ℕ, LocalNormSections.Construction.NormFrameOpen q L d

def localTraceSection (U : TraceFrameOpen q L)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.pullback q).sheaf) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.2.openSet.toScheme ⟶ (L.pullback U.2.openSet.ι).sheaf :=
  FramedTraceSection.Construction.framedTraceSection (q ∣_ U.2.openSet) U.2.frame.hom (LocalNormSections.Construction.localNormInput U.2.openSet z)

theorem traceFrameOpens_cover [Flat q] [LocallyOfFinitePresentation q] (y : Y) :
    ∃ U : TraceFrameOpen q L, y ∈ U.2.openSet := by
  obtain ⟨U, hU, hyU, d, ⟨b⟩⟩ := Quotients.FiniteDescent.SchemeTrivializationBasis.Construction.SchemeTrivialization.exists_basis_neighborhood q y
  obtain ⟨V, hyV, ⟨e⟩⟩ := L.locallyTrivial y
  obtain ⟨_, ⟨W : Y.Opens, hW, rfl⟩, hyW, hWU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ U ⊓ V from ⟨hyU, hyV⟩)
      (U ⊓ V).isOpen
  have : IsAffine U.toScheme := hU
  have : IsAffine W.toScheme := hW
  obtain ⟨bW⟩ := Quotients.FiniteDescent.AffineBasis.Construction.AffineBasisTransfer.restrictLE q W U (hWU.trans inf_le_left) b
  exact ⟨⟨d, ⟨W, hW, bW, (L.frameRestrict (hWU.trans inf_le_right) e).symm⟩⟩, hyW⟩

theorem traceFrameOpens_isBasis [Flat q] [LocallyOfFinitePresentation q] :
    Opens.IsBasis (Set.range (fun U : TraceFrameOpen q L => U.2.openSet)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro V y hy
  obtain ⟨U, hyU⟩ := traceFrameOpens_cover q L y
  obtain ⟨_, ⟨W : Y.Opens, hW, rfl⟩, hyW, hWV⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ V ⊓ U.2.openSet from ⟨hy, hyU⟩) (V ⊓ U.2.openSet).isOpen
  exact ⟨W, ⟨⟨U.1, U.2.restrictAffine W hW (hWV.trans inf_le_right)⟩, rfl⟩,
    hyW, hWV.trans inf_le_left⟩

set_option backward.isDefEq.respectTransparency false in
theorem localTraceSection_refine (V U : TraceFrameOpen q L) (h : V.2.openSet ≤ U.2.openSet)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.pullback q).sheaf) :
    OpenSectionGluing.Construction.refineSectionTo (Y.homOfLE h) U.2.openSet.ι V.2.openSet.ι (Y.homOfLE_ι h)
      (localTraceSection q L U z) = localTraceSection q L V z := by
  have : IsAffine U.2.openSet.toScheme := U.2.affine
  have : IsAffine V.2.openSet.toScheme := V.2.affine
  have : IsAffine (q ⁻¹ᵁ U.2.openSet).toScheme := isAffine_of_isAffineHom (q ∣_ U.2.openSet)
  have : IsAffine (q ⁻¹ᵁ V.2.openSet).toScheme := isAffine_of_isAffineHom (q ∣_ V.2.openSet)
  let j := X.homOfLE (q.preimage_mono h)
  let i := Y.homOfLE h
  have hj : j ≫ (q ⁻¹ᵁ U.2.openSet).ι = (q ⁻¹ᵁ V.2.openSet).ι := X.homOfLE_ι _
  have hi : i ≫ U.2.openSet.ι = V.2.openSet.ι := Y.homOfLE_ι h
  have hs : IsPullback j (q ∣_ V.2.openSet) (q ∣_ U.2.openSet) i := by
    apply IsPullback.of_right (t := (isPullback_morphismRestrict q U.2.openSet).flip)
    · simpa only [j, i, Scheme.homOfLE_ι] using (isPullback_morphismRestrict q V.2.openSet).flip
    · exact (morphismRestrict_homOfLE q V.2.openSet U.2.openSet h).symm
  have hc : (j ≫ (q ⁻¹ᵁ U.2.openSet).ι) ≫ q = (q ∣_ V.2.openSet) ≫ (i ≫ U.2.openSet.ι) := by
    rw [hj, hi]
    exact (morphismRestrict_ι q V.2.openSet).symm
  have htrace := TraceSquareComposition.Construction.traceSquareSection_comp q (q ∣_ U.2.openSet) (q ∣_ V.2.openSet)
    (q ⁻¹ᵁ U.2.openSet).ι U.2.openSet.ι j i (morphismRestrict_ι q U.2.openSet).symm hs hc
    U.2.basis L U.2.frame z
  exact (congrArg (fun s => s ≫ (Scheme.Modules.pullbackCongr hi).hom.app L.sheaf) htrace).trans
    (TraceSquareComposition.Construction.traceSquareSection_congr q (q ∣_ V.2.openSet) (j ≫ (q ⁻¹ᵁ U.2.openSet).ι)
      (q ⁻¹ᵁ V.2.openSet).ι (i ≫ U.2.openSet.ι) V.2.openSet.ι hc
      (morphismRestrict_ι q V.2.openSet).symm hj hi L
      (NormSquareComposition.Construction.compositeNormFrame U.2.openSet.ι i L U.2.frame) V.2.frame z)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LocalTraceSections.Construction
