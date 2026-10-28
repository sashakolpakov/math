import OAI.AlgebraicGeometry.FormalGeometry.Completion.TranslationSquare
import OAI.AlgebraicGeometry.FormalGeometry.Completion.OppositeTranslations
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SymmetricAffine

/-! # Projectivity -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Projectivity

noncomputable section

/-! Actual projectivity of a proper smooth geometrically integral
commutative group over an algebraically closed field. The ample bundle is
constructed from an affine section neighborhood and the proved cube identity. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

theorem lineBundle_isAmple_of_affine_section (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ⟶ L.sheaf)
    (hne : (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s : Set A.left).Nonempty)
    (haff : IsAffineOpen (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s)) : L.IsAmple := by
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have : A.left.IsSeparated := ⟨by
    rw [← terminal.comp_from A.hom]
    infer_instance⟩
  apply L.isAmple_iff_tensorPower.mpr
  refine ⟨isCompact_univ, fun x => ?_⟩
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints
    (Set.singleton_nonempty x).closure isClosed_closure.isLocallyClosed
  let p : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A :=
    Over.homMk (pointOfClosedPoint A.hom y hyc) (pointOfClosedPoint_comp A.hom y hyc)
  have hp : p.left (IsLocalRing.closedPoint K) = y := pointOfClosedPoint_apply A.hom y hyc _
  obtain ⟨a, hapos, haneg⟩ := OppositeTranslations.Construction.opposite_translations_meet A (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) hne p
  rw [hp] at hapos haneg
  let f := (GrpObj.mulRight a).hom.left
  let g := (GrpObj.mulRight a⁻¹).hom.left
  let t₀ := Quotients.FiniteDescent.BinaryTensorId.Construction.BinaryTensorMap.tensorSection (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection g s)
  let e := TranslationSquare.Construction.oppositeTranslationSquareIso A L a
  let t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ⟶ (L.tensorPower 2).sheaf := t₀ ≫ e.hom
  have ht : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t =
      f ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s ⊓ g ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s := by
    exact (AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso t₀ e).trans
      ((Quotients.FiniteDescent.TensorSection.Construction.TensorSectionLocus.nonvanishing (L := L.pullback f) (M := L.pullback g)
        (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection g s)).trans
        (congrArg₂ (· ⊓ ·) (Quotients.FiniteDescent.SectionBase.Construction.SectionBaseChange.nonvanishing_pullback f L s)
          (Quotients.FiniteDescent.SectionBase.Construction.SectionBaseChange.nonvanishing_pullback g L s)))
  have hyt : y ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t := ht.symm ▸ ⟨hapos, haneg⟩
  have hxt : x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t :=
    (specializes_iff_mem_closure.mpr hy).mem_open (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t).isOpen hyt
  refine ⟨2, by omega, t, hxt, ?_⟩
  rw [ht]
  exact (haff.preimage_of_isIso f).inf (haff.preimage_of_isIso g)

/-- A symmetric ample line bundle is produced from the actual group geometry. -/
theorem exists_symmetric_ample_lineBundle :
    ∃ L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left, L.IsAmple ∧
      Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf) := by
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  let x : A.left := Classical.choice inferInstance
  obtain ⟨L, s, hx, hs, hsym⟩ := Quotients.FiniteDescent.SymmetricAffine.Construction.SymmetricAffineSections.exists_for_group A x
  exact ⟨L, lineBundle_isAmple_of_affine_section A L s ⟨x, hx⟩ hs, hsym⟩

theorem geometric_group_projectivePresentation :
    Nonempty (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A) := by
  obtain ⟨L, hL, _⟩ := exists_symmetric_ample_lineBundle A
  exact hL.exists_projectivePresentation A.hom

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Projectivity
