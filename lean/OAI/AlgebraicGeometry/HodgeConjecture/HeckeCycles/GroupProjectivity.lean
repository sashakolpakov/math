import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PairedTranslateCover
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TranslateLineSquare
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineComplement
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorSection
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionBase
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeSmooth
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.ProjectivePresentation

/-! # Group Projectivity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupProjectivity.CM

noncomputable section

/-! Construct an ample line bundle and an actual projective embedding
on a proper smooth connected commutative group. Opposite translated
sections of one affine divisor are sections of its square and give
affine neighborhoods covering the original group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {K : Type} [Field K] [IsAlgClosed K]
  (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]

local notation "Point" => 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A

def squareSection (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ⟶ L.sheaf)
    (b : Point) : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ⟶ (L.tensorPower 2).sheaf :=
  Quotients.FiniteDescent.BinaryTensorId.Construction.BinaryTensorMap.tensorSection
    (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A b).hom s)
    (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A b⁻¹).hom s) ≫
      (Classical.choice (TranslateLineSquare.CM.square_iso A L b)).inv

theorem squareSection_nonvanishing
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ⟶ L.sheaf) (b : Point) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (squareSection A L s b) =
      PairedTranslateCover.CM.pairedOpen A (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) b := by
  let e := Classical.choice (TranslateLineSquare.CM.square_iso A L b)
  have he := AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso
    (Quotients.FiniteDescent.BinaryTensorId.Construction.BinaryTensorMap.tensorSection
      (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A b).hom s)
      (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A b⁻¹).hom s)) e.symm
  have ht := Quotients.FiniteDescent.TensorSection.Construction.TensorSectionLocus.nonvanishing
    (L := L.pullback (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A b).hom)
    (M := L.pullback (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A b⁻¹).hom)
    (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A b).hom s)
    (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A b⁻¹).hom s)
  exact he.trans (ht.trans (congrArg₂ (fun U V : A.left.Opens => U ⊓ V)
    (Quotients.FiniteDescent.SectionBase.Construction.SectionBaseChange.nonvanishing_pullback (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A b).hom L s)
    (Quotients.FiniteDescent.SectionBase.Construction.SectionBaseChange.nonvanishing_pullback (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A b⁻¹).hom L s)))

theorem square_ample (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ⟶ L.sheaf)
    (ha : IsAffineOpen (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s))
    (hne : ((AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s : A.left.Opens) : Set A.left).Nonempty) :
    (L.tensorPower 2).IsAmple := by
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : A.left.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from A.hom]
    infer_instance⟩
  refine ⟨isCompact_univ, fun x => ?_⟩
  obtain ⟨b, hb⟩ := PairedTranslateCover.CM.covers A (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) hne x
  refine ⟨1, Nat.zero_lt_one, L.tensorPower 2, AbelianModuli.HilbertConstruction.Tensor.Powers.isTensorPower_one _, squareSection A L s b, ?_, ?_⟩
  · rwa [squareSection_nonvanishing]
  · rw [squareSection_nonvanishing]
    exact PairedTranslateCover.CM.affine A _ ha b

theorem exists_ample : ∃ L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left, L.IsAmple := by
  have : IsReduced A.left := Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced.reduced_of_smooth_field A.hom
  have : IrreducibleSpace A.left := Quotients.FiniteDescent.GroupIrreducibleOf.Construction.GroupIrreducible.irreducibleSpace_of_connected_group A
  have : IsIntegral A.left := isIntegral_of_irreducibleSpace_of_isReduced A.left
  have : A.left.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from A.hom]
    infer_instance⟩
  let x : A.left := (MonObj.one (X := A)).left (IsLocalRing.closedPoint K)
  obtain ⟨U, hU, hx, _⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp A.left.isBasis_affineOpens
    (show x ∈ (⊤ : A.left.Opens) from trivial)
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  obtain ⟨L, s, hs⟩ := Quotients.FiniteDescent.AffineComplement.Construction.AffineComplementDivisor.exists_lineBundle A.hom ⟨U, hU⟩
  refine ⟨L.tensorPower 2, square_ample A L s ?_ ?_⟩
  · rwa [hs]
  · rw [hs]
    exact ⟨x, hx⟩

theorem projective : Nonempty (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A) := by
  obtain ⟨L, hL⟩ := exists_ample A
  exact hL.exists_projectivePresentation A.hom

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupProjectivity.CM
