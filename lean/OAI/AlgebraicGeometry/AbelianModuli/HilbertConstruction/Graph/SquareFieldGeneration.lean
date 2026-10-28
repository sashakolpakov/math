import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.SquareGeneration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.DegreeGenerationFieldDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Square Field Generation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The canonical graph bundle has a globally generated square over every
field at tame full level. The tensor exponent is independent of the object. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_square_pointwise_sections_overField
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    ∀ x : A.abelian.scheme.left,
      ∃ s : Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower 2).sheaf,
        x ∈ Ample.LineBundles.sectionNonvanishing s := by
  let φ : CommRingCat.of K ⟶ CommRingCat.of (AlgebraicClosure K) :=
    CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))
  let B := A.pullback (Spec.map φ)
  let a := pullback.fst A.abelian.scheme.hom (Spec.map φ)
  have hNF : (N : AlgebraicClosure K) ≠ 0 := by
    intro hz
    apply hNk
    apply (algebraMap K (AlgebraicClosure K)).injective
    simpa only [map_natCast, map_zero] using hz
  apply (A.graphBundle.tensorPower 2).pointwise_sections_of_fieldExtension A.abelian.scheme.hom φ
  intro y
  obtain ⟨t, ht⟩ := B.graphBundle_square_pointwise_sections hN hNF y
  let e : (B.graphBundle.tensorPower 2).sheaf ≅
      ((A.graphBundle.tensorPower 2).pullback a).sheaf :=
    (TensorPower.Maps.tensorPowerFunctor B.abelian.scheme.left 2).mapIso (A.graphBundle_baseChangeIso (Spec.map φ)) ≪≫
      (A.graphBundle.powerBaseChangeIso a 2).symm
  exact ⟨t ≫ e.hom, (congrArg (fun U : B.abelian.scheme.left.Opens => y ∈ U)
    (Ample.Powers.sectionNonvanishing_comp_iso t e)).mpr ht⟩

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_square_finite_section_cover_overField
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    ∃ (n : ℕ) (s : Fin (n + 1) →
      (Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower 2).sheaf)),
      ∀ x : A.abelian.scheme.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i) := by
  have : CompactSpace A.abelian.scheme.left :=
    QuasiCompact.compactSpace_of_compactSpace A.abelian.scheme.hom
  exact (A.graphBundle.tensorPower 2).finite_section_cover_of_pointwise
    (A.graphBundle_square_pointwise_sections_overField hN hNk)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
