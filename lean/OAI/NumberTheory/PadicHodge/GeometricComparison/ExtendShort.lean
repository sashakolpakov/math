import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Extend Short -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ExtendShort.ExtendShortExact

noncomputable section

/-! Extension by zero preserves actual short exact sequences of complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (e : c.Embedding c') (S : ShortComplex (HomologicalComplex C c))

def degreeIso {i : ι} {j : ι'} (h : e.f i = j) :
    ((S.map (e.extendFunctor C)).map (HomologicalComplex.eval C c' j)) ≅
      S.map (HomologicalComplex.eval C c i) :=
  ShortComplex.isoMk (S.X₁.extendXIso e h) (S.X₂.extendXIso e h) (S.X₃.extendXIso e h)
    (by
      change (S.X₁.extendXIso e h).hom ≫ S.f.f i =
        (HomologicalComplex.extendMap S.f e).f j ≫ (S.X₂.extendXIso e h).hom
      rw [HomologicalComplex.extendMap_f _ _ h]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    (by
      change (S.X₂.extendXIso e h).hom ≫ S.g.f i =
        (HomologicalComplex.extendMap S.g e).f j ≫ (S.X₃.extendXIso e h).hom
      rw [HomologicalComplex.extendMap_f _ _ h]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

theorem shortExact (hS : S.ShortExact) : (S.map (e.extendFunctor C)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro j
  by_cases hj : ∃ i, e.f i = j
  · obtain ⟨i, hi⟩ := hj
    exact (ShortComplex.shortExact_iff_of_iso (degreeIso e S hi)).mpr
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS i)
  · have h (K : HomologicalComplex C c) : IsZero ((K.extend e).X j) :=
      K.isZero_extend_X e j (by simpa using hj)
    exact (ShortComplex.Splitting.ofIsZeroOfIsIso _ (h S.X₁)
      ((h S.X₂).isIso (h S.X₃) _)).shortExact

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ExtendShort.ExtendShortExact
