import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.IsomorphismDescent
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Isomorphism Field Descent -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.IsomorphismFieldDescent

noncomputable section

/-! The relative isomorphism condition descends across field extensions;
an isomorphic test family therefore has isomorphic fibers at its image points. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem specMap_field_faithfullyFlat {K L : Type u} [Field K] [Field L]
    (φ : CommRingCat.of K ⟶ CommRingCat.of L) :
    Surjective (Spec.map φ) ∧ Flat (Spec.map φ) ∧ QuasiCompact (Spec.map φ) := by
  let : Algebra K L := φ.hom.toAlgebra
  refine ⟨⟨fun x => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩, ?_, inferInstance⟩
  exact Flat.SpecMap_iff.mpr (inferInstanceAs (Module.Flat K L))

variable {X Y B T : Scheme.{u}}

theorem relativeMorphismBaseChange_isIso_of_field_extension
    (f : X ⟶ Y) (q : Y ⟶ B)
    {K L : Type u} [Field K] [Field L]
    (b : Spec (.of K) ⟶ B) (φ : CommRingCat.of K ⟶ CommRingCat.of L)
    (h : IsIso (MorphismIsomorphismLocus.relativeMorphismBaseChange f q (Spec.map φ ≫ b))) :
    IsIso (MorphismIsomorphismLocus.relativeMorphismBaseChange f q b) := by
  obtain ⟨hs, hf, hc⟩ := specMap_field_faithfullyFlat φ
  let := hs
  let := hf
  let := hc
  exact IsomorphismDescent.relativeMorphismBaseChange_isIso_of_faithfullyFlat f q b (Spec.map φ) h

theorem relativeMorphismBaseChange_isIso_at_image_point
    (f : X ⟶ Y) (q : Y ⟶ B) (g : T ⟶ B)
    (h : IsIso (MorphismIsomorphismLocus.relativeMorphismBaseChange f q g)) (t : T) :
    IsIso (MorphismIsomorphismLocus.relativeMorphismBaseChange f q (B.fromSpecResidueField (g t))) := by
  apply relativeMorphismBaseChange_isIso_of_field_extension f q
    (B.fromSpecResidueField (g t)) (g.residueFieldMap t)
  exact (congrArg
    (fun a : Spec (T.residueField t) ⟶ B => IsIso (MorphismIsomorphismLocus.relativeMorphismBaseChange f q a))
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g t)).mpr
    (IsomorphismDescent.relativeMorphismBaseChange_isIso_comp f q g (T.fromSpecResidueField t) h)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.IsomorphismFieldDescent
