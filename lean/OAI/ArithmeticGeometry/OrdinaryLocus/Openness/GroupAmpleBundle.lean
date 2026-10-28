import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GeometricCube
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OppositeTranslationNeighborhood
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SymmetricAffine
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.ProjectivePresentation

/-! # Group Ample Bundle -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GroupAmpleBundle.Construction

noncomputable section

/-! A symmetric ample line bundle on a smooth proper connected commutative group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {K : Type} [Field K] [IsAlgClosed K]
variable (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]

theorem square_lineBundle_affineSection_at
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (s : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ⟶ L.sheaf)
    (hs : IsAffineOpen (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s))
    (hne : ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s : A.left.Opens) : Set A.left).Nonempty) (x : A.left) :
    ∃ t : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ⟶ (L.tensor L).sheaf,
      x ∈ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t ∧ IsAffineOpen (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t) := by
  have : GeometricallyIntegral A.hom := AlgebraicGeometry.Quotients.FiniteDescent.AbelianGeometric.Construction.AbelianGeometricIntegral.geometricallyIntegral A
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : A.left.IsSeparated := ⟨by rw [← CategoryTheory.Limits.terminal.comp_from A.hom]; infer_instance⟩
  obtain ⟨a, ha⟩ := OppositeTranslationNeighborhood.Construction.exists_opposite_translate_neighborhood A (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) hne x
  let f := (AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a).hom
  let g := (AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a⁻¹).hom
  let q := AlgebraicGeometry.Quotients.FiniteDescent.BinaryTensorId.Construction.BinaryTensorMap.tensorSection (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection g s)
  have hq : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing q = f ⁻¹ᵁ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s ⊓ g ⁻¹ᵁ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s :=
    (AlgebraicGeometry.Quotients.FiniteDescent.TensorSection.Construction.TensorSectionLocus.nonvanishing (L := L.pullback f) (M := L.pullback g)
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection g s)).trans
      (congrArg₂ (· ⊓ ·) (AlgebraicGeometry.Quotients.FiniteDescent.SectionBase.Construction.SectionBaseChange.nonvanishing_pullback f L s)
        (AlgebraicGeometry.Quotients.FiniteDescent.SectionBase.Construction.SectionBaseChange.nonvanishing_pullback g L s))
  obtain ⟨e⟩ := GeometricCube.Construction.lineBundleTranslation_square A L a
  let e' : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj L.sheaf)
      ((Scheme.Modules.pullback g).obj L.sheaf) ≅ (L.tensor L).sheaf := e
  refine ⟨q ≫ e'.hom, ?_, ?_⟩
  · rw [AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso, hq]
    exact ha
  · rw [AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso, hq]
    exact (hs.preimage_of_isIso f).inf (hs.preimage_of_isIso g)

theorem square_lineBundle_isAmple
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (s : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ⟶ L.sheaf)
    (hs : IsAffineOpen (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s))
    (hne : ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s : A.left.Opens) : Set A.left).Nonempty) :
    (L.tensor L).IsAmple := by
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  refine ⟨isCompact_univ, fun x => ?_⟩
  obtain ⟨t, ht, ha⟩ := square_lineBundle_affineSection_at A L s hs hne x
  exact ⟨1, Nat.zero_lt_one, L.tensor L, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.isTensorPower_one _, t, ht, ha⟩

theorem exists_symmetric_ample_lineBundle :
    ∃ L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left, L.IsAmple ∧
      Nonempty ((L.pullback ((𝟙 A : A ⟶ A)⁻¹).left).sheaf ≅ L.sheaf) := by
  let x := (η[A]).left (IsLocalRing.closedPoint K)
  obtain ⟨L, s, hx, hs, ⟨e⟩⟩ := AlgebraicGeometry.Quotients.FiniteDescent.SymmetricAffine.Construction.SymmetricAffineSections.exists_for_group A x
  refine ⟨L.tensor L, square_lineBundle_isAmple A L s hs ⟨x, hx⟩, ?_⟩
  exact ⟨AlgebraicGeometry.Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.tensorIso ((𝟙 A : A ⟶ A)⁻¹).left L L ≪≫
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr e e⟩

theorem group_projectivePresentation : Nonempty (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A) := by
  obtain ⟨L, hL, _⟩ := exists_symmetric_ample_lineBundle A
  exact hL.exists_projectivePresentation A.hom

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GroupAmpleBundle.Construction
