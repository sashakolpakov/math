import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NontrivialHomogeneousLineCohomology
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.FieldHomogeneityBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FaithfulFlatCohomologyVanishing
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Homogeneous Line Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.HomogeneousLineCohomology

noncomputable section

/-! Nontrivial homogeneous projective line bundles have zero cohomology
over any field. Actual triviality and cohomology descend from the
algebraic closure along the original Cartesian scalar-extension square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {K : Type} [Field K] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (L : Line.Bundles.LineBundle A.scheme.left)

theorem lineBundle_nontrivial_after_fieldExtension
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (hne : ¬ Nonempty (L.sheaf ≅ Line.Bundles.structureModule A.scheme.left))
    {K' : Type} [Field K'] (c : Spec (.of K') ⟶ Spec (.of K)) :
    ¬ Nonempty ((L.pullback (pullback.fst A.scheme.hom c)).sheaf ≅
      Line.Bundles.structureModule (A.pullback c).scheme.left) := by
  rintro ⟨e⟩
  apply hne
  exact Picard.ThetaConstruction.FieldFrameReflection.Geometric.field_line_trivial_of_cartesian_trivial P
    η[A.scheme].left η[A.scheme].w L
    (Classical.choice (RepresentationTheory.Theta.Geometric.LineBundleFieldTriviality.lineBundle_over_field_trivial K
      (L.pullback η[A.scheme].left)))
    (pullback.fst A.scheme.hom c) (pullback.snd A.scheme.hom c) c
    (IsPullback.of_hasPullback A.scheme.hom c) e

theorem nontrivialHomogeneousLine_cohomology_vanish_overField
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (hL : ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (Line.Bundles.LineBundle.classOf L))
    (hne : ¬ Nonempty (L.sheaf ≅ Line.Bundles.structureModule A.scheme.left)) (n : ℕ) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H L.sheaf n) := by
  let φ : CommRingCat.of K ⟶ CommRingCat.of (AlgebraicClosure K) :=
    CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))
  let c := Spec.map φ
  have : A.scheme.left.IsSeparated :=
    ⟨by rw [← terminal.comp_from A.scheme.hom]; infer_instance⟩
  have : CompactSpace A.scheme.left :=
    QuasiCompact.compactSpace_of_compactSpace A.scheme.hom
  have hp := NontrivialHomogeneousLineCohomology.nontrivialHomogeneousLine_cohomology_vanish (A.pullback c)
    (L.pullback (pullback.fst A.scheme.hom c))
    (Picard.ThetaConstruction.FieldHomogeneityBaseChange.Geometric.homogeneousLine_baseChange A L c hL)
    (lineBundle_nontrivial_after_fieldExtension A L P hne c) n
  exact (FaithfulFlatCohomologyVanishing.fieldExtensionLineBundle_cohomology_vanish_iff
    (IsPullback.of_hasPullback A.scheme.hom c) L n).mp hp

theorem nontrivialHomogeneousLine_cohomology_isZero_overField
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (hL : ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (Line.Bundles.LineBundle.classOf L))
    (hne : ¬ Nonempty (L.sheaf ≅ Line.Bundles.structureModule A.scheme.left)) (n : ℕ) :
    IsZero ((Zariski.Cohomology.ZariskiCohomology.zariskiFunctor A.scheme.left n).obj L.sheaf) :=
  AddCommGrpCat.isZero_iff_subsingleton.mpr
    (nontrivialHomogeneousLine_cohomology_vanish_overField A L P hL hne n)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.HomogeneousLineCohomology
