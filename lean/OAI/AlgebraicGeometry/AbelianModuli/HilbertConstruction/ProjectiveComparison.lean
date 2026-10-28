import Mathlib.Algebra.Homology.DerivedCategory.SmallShiftedHom
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveBasic
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-! # Projective Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

open _root_.CochainComplex

/- Adapted to HilbertConstruction-local theorem names. Retain the comparison of
quasi-isomorphisms and homotopy equivalences between K-projective complexes. -/

universe w v u

open _root_.CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

open Localization DerivedCategory

open _root_.HomologicalComplex

lemma ProjectiveBasic.CochainComplex.IsKProjective.Qh_map_bijective [HasDerivedCategory C]
    (K : CochainComplex C ℤ) (L : HomotopyCategory C (.up ℤ))
    [ProjectiveBasic.CochainComplex.IsKProjective K] :
    Function.Bijective (DerivedCategory.Qh.map :
      ((HomotopyCategory.quotient _ _).obj K ⟶ L) → _) :=
  (ProjectiveBasic.CochainComplex.IsKProjective.leftOrthogonal K).map_bijective_of_isTriangulated _ _

attribute [local instance] HasDerivedCategory.standard in
lemma ProjectiveBasic.CochainComplex.IsKProjective.quasiIso_iff {K L : CochainComplex C ℤ} [ProjectiveBasic.CochainComplex.IsKProjective K] [ProjectiveBasic.CochainComplex.IsKProjective L] (f : K ⟶ L) :
    QuasiIso f ↔ homotopyEquivalences C (.up ℤ) f := by
  refine ⟨fun _ ↦ ?_, fun hf ↦ homotopyEquivalences_le_quasiIso _ _ _ hf⟩
  rw [← HomotopyCategory.inverseImage_quotient_isomorphisms,
    MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff]
  obtain ⟨g, hg⟩ := (ProjectiveBasic.CochainComplex.IsKProjective.Qh_map_bijective _ _).surjective
    ((quotientCompQhIso C).hom.app L ≫ inv (Q.map f) ≫ (quotientCompQhIso C).inv.app K)
  refine ⟨g, (ProjectiveBasic.CochainComplex.IsKProjective.Qh_map_bijective _ _).injective ?_, (ProjectiveBasic.CochainComplex.IsKProjective.Qh_map_bijective _ _).injective ?_⟩
  · simp [hg]
  · simp [hg, ← quotientCompQhIso_inv_naturality f, -NatTrans.naturality]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
