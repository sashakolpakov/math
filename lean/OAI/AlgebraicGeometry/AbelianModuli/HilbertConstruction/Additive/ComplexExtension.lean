import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.Embedding.TruncGE
import Mathlib.Algebra.Homology.Additive

/-! # Complex Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.ComplexExtension

noncomputable section

/-! Additive functors commute with extension by zero. A complex already supported on an embedded interval has the same exactness as its restriction, including its endpoints. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u v w u' v'
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {ι ι' : Type w} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (F : C ⥤ D) [F.Additive] (K : HomologicalComplex C c) (e : c.Embedding c')

def additiveExtendXIso (j : ι') :
    F.obj ((K.extend e).X j) ≅ (((F.mapHomologicalComplex c).obj K).extend e).X j := by
  classical
  exact if h : ∃ i, e.f i = j then
      F.mapIso (K.extendXIso e h.choose_spec) ≪≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e h.choose_spec).symm
    else
      IsZero.iso (F.map_isZero (K.isZero_extend_X e j (by simpa using h)))
        (((F.mapHomologicalComplex c).obj K).isZero_extend_X e j (by simpa using h))

theorem additiveExtendXIso_in {i : ι} {j : ι'} (h : e.f i = j) :
    additiveExtendXIso F K e j = F.mapIso (K.extendXIso e h) ≪≫
      (((F.mapHomologicalComplex c).obj K).extendXIso e h).symm := by
  classical
  have hex : ∃ k, e.f k = j := ⟨i, h⟩
  simp only [additiveExtendXIso, dite_eq_left hex]
  have he : hex.choose = i := e.injective_f (hex.choose_spec.trans h.symm)
  subst i
  rfl

def additiveExtendIso :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e := by
  classical
  refine HomologicalComplex.Hom.isoOfComponents (additiveExtendXIso F K e) ?_
  intro i' j' _
  by_cases hi : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi
    by_cases hj : ∃ j, e.f j = j'
    · obtain ⟨j, hj⟩ := hj
      rw [additiveExtendXIso_in F K e hi, additiveExtendXIso_in F K e hj]
      let fi : F.obj ((K.extend e).X i') ≅ F.obj (K.X i) := F.mapIso (K.extendXIso e hi)
      let fj : F.obj ((K.extend e).X j') ≅ F.obj (K.X j) := F.mapIso (K.extendXIso e hj)
      let gi : (((F.mapHomologicalComplex c).obj K).extend e).X i' ≅ F.obj (K.X i) :=
        ((F.mapHomologicalComplex c).obj K).extendXIso e hi
      let gj : (((F.mapHomologicalComplex c).obj K).extend e).X j' ≅ F.obj (K.X j) :=
        ((F.mapHomologicalComplex c).obj K).extendXIso e hj
      have hF : F.map ((K.extend e).d i' j') = fi.hom ≫ F.map (K.d i j) ≫ fj.inv :=
        (congrArg F.map (K.extend_d_eq e hi hj)).trans
          ((F.map_comp _ _).trans (congrArg (fun k => fi.hom ≫ k) (F.map_comp _ _)))
      have hD : (((F.mapHomologicalComplex c).obj K).extend e).d i' j' =
          gi.hom ≫ F.map (K.d i j) ≫ gj.inv :=
        ((F.mapHomologicalComplex c).obj K).extend_d_eq e hi hj
      change (fi.hom ≫ gi.inv) ≫ (((F.mapHomologicalComplex c).obj K).extend e).d i' j' =
        F.map ((K.extend e).d i' j') ≫ fj.hom ≫ gj.inv
      rw [hD, hF]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    · exact (((F.mapHomologicalComplex c).obj K).isZero_extend_X e j'
        (by simpa using hj)).eq_of_tgt _ _
  · exact (F.map_isZero (K.isZero_extend_X e i' (by simpa using hi))).eq_of_src _ _

theorem additive_extend_acyclic
    (hK : ((F.mapHomologicalComplex c).obj K).Acyclic) :
    ((F.mapHomologicalComplex c').obj (K.extend e)).Acyclic := by
  intro j'
  apply (exactAt_iff_of_quasiIsoAt (additiveExtendIso F K e).hom j').mpr
  by_cases h : ∃ j, e.f j = j'
  · obtain ⟨j, hj⟩ := h
    exact (((F.mapHomologicalComplex c).obj K).extend_exactAt_iff e hj).mpr (hK j)
  · exact ((F.mapHomologicalComplex c).obj K).extend_exactAt e j' (by simpa using h)

theorem supported_restriction_exactAt_iff
    (L : HomologicalComplex C c') [e.IsTruncGE] [L.IsStrictlySupported e] (j : ι) :
    (L.restriction e).ExactAt j ↔ L.ExactAt (e.f j) := by
  have : IsIso (L.restrictionToTruncGE' e) := HomologicalComplex.Hom.isIso_of_components _
  calc
    (L.restriction e).ExactAt j ↔ (L.truncGE' e).ExactAt j :=
      exactAt_iff_of_quasiIsoAt (L.restrictionToTruncGE' e) j
    _ ↔ (L.truncGE e).ExactAt (e.f j) := ((L.truncGE' e).extend_exactAt_iff e rfl).symm
    _ ↔ L.ExactAt (e.f j) :=
      (exactAt_iff_of_quasiIsoAt (L.πTruncGE e) (e.f j)).symm

theorem supported_restriction_acyclic
    (L : HomologicalComplex C c') [e.IsTruncGE] [L.IsStrictlySupported e]
    (hL : L.Acyclic) : (L.restriction e).Acyclic := by
  intro j
  exact (supported_restriction_exactAt_iff e L j).mpr (hL (e.f j))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.ComplexExtension
