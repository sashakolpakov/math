import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.FinePELPoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.CountableRankSchemePoints
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Analysis.Complex.Cardinality

/-! # PEL Complex Open Detection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PELComplexOpenDetection.Construction

noncomputable section

/-! An open subset of the original complex fine PEL scheme which
contains all complex-valued points is the whole scheme. Every geometric
point factors through a countable field model, whose complex coefficient
spectrum has enough rational points to detect the open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
theorem finePEL_complex_open_eq_top_of_complex_points
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s N : ℕ} [NeZero N]
    {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K} (Z : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hZ : Z.IsFine)
    (κ : K →+* ℂ) (U : (Z.complexFiber κ).left.Opens)
    (hU : ∀ p : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ Z.complexFiber κ,
      p.left (IsLocalRing.closedPoint ℂ) ∈ U) : U = ⊤ := by
  apply top_unique
  intro z _
  let k := AlgebraicClosure ((Z.complexFiber κ).left.residueField z)
  let p : Spec (.of k) ⟶ (Z.complexFiber κ).left :=
    Spec.map (CommRingCat.ofHom (algebraMap ((Z.complexFiber κ).left.residueField z) k)) ≫
      (Z.complexFiber κ).left.fromSpecResidueField z
  let a := p ≫ pullback.fst Z.space.hom (Spec.map (CommRingCat.ofHom κ))
  let j : K →+* k := (Spec.preimage (a ≫ Z.space.hom)).hom
  let x : Over.mk (Spec.map (CommRingCat.ofHom j)) ⟶ Z.space :=
    Over.homMk a (Spec.map_preimage (a ≫ Z.space.hom)).symm
  obtain ⟨F, jF, hF, _, _, b, hb⟩ := IsogenyQuotient.Countable.FinePELPoints.Construction.finePEL_geometric_point_has_countable_model Z hZ k j x
  let : Countable F := hF
  let : Algebra K ℂ := κ.toAlgebra
  let : Algebra K F := jF.toAlgebra
  have : Uncountable ℂ := Complex.ofReal_injective.uncountable
  have hp := IsogenyQuotient.Countable.CountableRankSchemePoints.Construction.countable_field_model_point_mem_open K ℂ F Z.space b U hU p
    (Spec.map (CommRingCat.ofHom F.subtype)) hb
  have he : p (IsLocalRing.closedPoint k) = z :=
    (Z.complexFiber κ).left.fromSpecResidueField_apply z _
  exact he ▸ hp

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PELComplexOpenDetection.Construction
