import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.Linear

/-! # Extend Linear Core -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ExtendLinearCore.ExtendLinear

noncomputable section

/-! Extension by zero is linear over the coefficient ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable (R : Type*) [CommRing R] (C : Type u) [Category.{v} C]
  [Preadditive C] [HasZeroObject C] [Linear R C]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')

instance linear : (e.extendFunctor C).Linear R where
  map_smul {K L} f r := by
    apply HomologicalComplex.Hom.ext
    funext j
    by_cases hj : ∃ i, e.f i = j
    · obtain ⟨i, hi⟩ := hj
      change (HomologicalComplex.extendMap (r • f) e).f j =
        r • (HomologicalComplex.extendMap f e).f j
      rw [HomologicalComplex.extendMap_f _ _ hi, HomologicalComplex.extendMap_f _ _ hi]
      change (K.extendXIso e hi).hom ≫ (r • f.f i) ≫ (L.extendXIso e hi).inv = _
      rw [Linear.smul_comp, Linear.comp_smul]
    · exact (L.isZero_extend_X e j (by simpa using hj)).eq_of_tgt _ _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ExtendLinearCore.ExtendLinear
