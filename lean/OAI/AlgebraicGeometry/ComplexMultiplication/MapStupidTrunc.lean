import OAI.Algebra.Homology.MapExtend
import OAI.Algebra.Homology.StupidTruncation

/-! # Map Stupid Trunc -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.MapStupidTrunc.HomologicalComplex

noncomputable section

open _root_.HomologicalComplex

/-! # Exact functorial mapping of the original filtration truncation

Applying an additive functor preserves the original truncation by form degree,
including its actual inclusion into the untruncated complex.
-/

open _root_.CategoryTheory Limits

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D) [F.Additive]
  {I J : Type*} {c : ComplexShape I} {c' : ComplexShape J}
  (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsTruncGE]

/-- Applying the actual coefficient functor commutes with truncation by degree. -/
def mapStupidTruncCanonicalIso :
    (F.mapHomologicalComplex c').obj (K.stupidTrunc e) ≅
      ((F.mapHomologicalComplex c').obj K).stupidTrunc e :=
  Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso F (K.restriction e) e

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- This comparison retains precisely the original inclusion of the truncation. -/
theorem mapStupidTruncCanonicalIso_comp_inclusion :
    (mapStupidTruncCanonicalIso F K e).hom ≫
        Algebra.Homology.StupidTruncation.HomologicalComplex.stupidTruncInclusion ((F.mapHomologicalComplex c').obj K) e =
      (F.mapHomologicalComplex c').map (Algebra.Homology.StupidTruncation.HomologicalComplex.stupidTruncInclusion K e) := by
  ext j
  by_cases hj : ∃ i, e.f i = j
  · obtain ⟨i, hi⟩ := hj
    subst j
    rw [comp_f, Functor.mapHomologicalComplex_map_f,
      Algebra.Homology.StupidTruncation.HomologicalComplex.stupidTruncInclusion_f _ e rfl, Algebra.Homology.StupidTruncation.HomologicalComplex.stupidTruncInclusion_f _ e rfl]
    change (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso F (K.restriction e) e).hom.f (e.f i) ≫ _ = _
    rw [Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso_hom_f _ _ _ rfl]
    simp only [stupidTruncXIso, Iso.trans_hom, eqToIso_refl, Iso.refl_hom,
      CategoryTheory.Category.comp_id]
    have hInv : (((F.mapHomologicalComplex c).obj (K.restriction e)).extendXIso e
        (i := i) rfl).inv =
      ((((F.mapHomologicalComplex c').obj K).restriction e).extendXIso e
        (i := i) rfl).inv := rfl
    rw [hInv]
    simp [CategoryTheory.Category.assoc]
  · exact (F.map_isZero (K.isZero_stupidTrunc_X e j (by simpa using hj))).eq_of_src _ _

end

end OAI.AlgebraicGeometry.ComplexMultiplication.MapStupidTrunc.HomologicalComplex
