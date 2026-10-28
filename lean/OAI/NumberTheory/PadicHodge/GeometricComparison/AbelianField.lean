import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.ComplementDivisor
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integrality
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GroupAmple
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatAmpleDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Abelian Field -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.AbelianField.AbelianFieldAmple

noncomputable section

/-! An abelian scheme over an arbitrary field has an ample line bundle, constructed from an affine complement and descended from the algebraic closure. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

theorem exists_ample {K : Type} [Field K] {g : ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K))) :
    ∃ L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left, L.IsAmple := by
  let : GeometricallyIntegral A.scheme.hom :=
    Integrality.GeometricIntegrality.of_smooth_geometricallyConnected A.scheme.hom
  let : IsIntegral A.scheme.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton A.scheme.hom
  let : A.scheme.left.IsSeparated := ⟨by
    rw [← terminal.comp_from A.scheme.hom]
    infer_instance⟩
  let x : A.scheme.left := Classical.choice inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    A.scheme.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  obtain ⟨L, s, hs⟩ := Affine.ComplementDivisor.AffineComplementDivisor.exists_lineBundle A.scheme.hom ⟨U, hU⟩
  let b : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  let B := A.pullback b
  let p : B.scheme.left ⟶ A.scheme.left := pullback.fst A.scheme.hom b
  let : IsAffineHom b := inferInstance
  let : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom.{0}) A.scheme.hom :=
    ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback⟩
  let : IsAffineHom p :=
    MorphismProperty.pullback_fst (P := @IsAffineHom.{0}) A.scheme.hom b inferInstance
  let : Surjective b := ⟨fun z => ⟨IsLocalRing.closedPoint (AlgebraicClosure K),
    Subsingleton.elim _ z⟩⟩
  let : Surjective p := inferInstanceAs (Surjective (pullback.fst A.scheme.hom b))
  let t : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.scheme.left ⟶ (L.pullback p).sheaf := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection p s
  have ht : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t = p ⁻¹ᵁ U :=
    (AlgebraicGeometry.Quotients.FiniteDescent.SectionBase.Construction.SectionBaseChange.nonvanishing_pullback p L s).trans (congrArg (fun V => p ⁻¹ᵁ V) hs)
  have hnonempty : (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t : Set B.scheme.left).Nonempty := by
    obtain ⟨y, hy⟩ := p.surjective x
    refine ⟨y, ?_⟩
    rw [ht]
    change p y ∈ U
    exact hy.symm ▸ hxU
  have haff : IsAffineOpen (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t) := by
    rw [ht]
    exact hU.preimage p
  have hL : (L.pullback p).IsAmple :=
    AlgebraicGeometry.AbelianScheme.TateComparison.GroupAmple.groupLineBundle_ample_of_affine_section B.scheme (L.pullback p) t hnonempty haff
  let : Field Γ(Spec (.of K), ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)).toField
  exact ⟨L, AlgebraicGeometry.PELModuli.IntegralModel.FlatAmpleDescent.properFlat_isAmple_of_flat_surjective_baseChange
    A.scheme.hom L p B.scheme.hom b (.of_hasPullback A.scheme.hom b)
    (HasRingHomProperty.appTop (P := @Flat) b inferInstance) hL⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.AbelianField.AbelianFieldAmple
