import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.Embedding.Restriction
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Supported Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SupportedRestriction

noncomputable section

/-! Restricting a complex to a shape containing its support preserves
its actual homology and quasi-isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (e : c.Embedding c') [e.IsRelIff]
  (K : HomologicalComplex C c') [K.IsStrictlySupported e]

def componentIso (j : ι') : ((K.restriction e).extend e).X j ≅ K.X j := by
  classical
  by_cases hj : ∃ i, e.f i = j
  · exact (K.restriction e).extendXIso e hj.choose_spec ≪≫ K.restrictionXIso e hj.choose_spec
  · exact ((K.restriction e).isZero_extend_X e j (by simpa using hj)).iso
      (K.isZero_X_of_isStrictlySupported e j (by simpa using hj))

theorem componentIso_image (i : ι) (j : ι') (h : e.f i = j) :
    componentIso e K j = (K.restriction e).extendXIso e h ≪≫ K.restrictionXIso e h := by
  classical
  have hj : ∃ k, e.f k = j := ⟨i, h⟩
  have haux (a b : ι) (ha : e.f a = j) (hb : e.f b = j) :
      (K.restriction e).extendXIso e ha ≪≫ K.restrictionXIso e ha =
        (K.restriction e).extendXIso e hb ≪≫ K.restrictionXIso e hb := by
    have hab : a = b := e.injective_f (ha.trans hb.symm)
    subst b
    rfl
  simp only [componentIso, dite_eq_left hj]
  exact haux _ _ _ _

def extensionIso : (K.restriction e).extend e ≅ K :=
  Hom.isoOfComponents (componentIso e K) (by
    intro i j hij
    by_cases hi : ∃ a, e.f a = i
    · obtain ⟨a, ha⟩ := hi
      by_cases hj : ∃ b, e.f b = j
      · obtain ⟨b, hb⟩ := hj
        rw [componentIso_image e K a i ha, componentIso_image e K b j hb,
          extend_d_eq _ e ha hb, restriction_d_eq _ e ha hb]
        simp only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc,
          Iso.inv_hom_id, Category.comp_id]
      · exact (K.isZero_X_of_isStrictlySupported e j (by simpa using hj)).eq_of_tgt _ _
    · exact ((K.restriction e).isZero_extend_X e i (by simpa using hi)).eq_of_src _ _)

theorem extensionIso_natural {L : HomologicalComplex C c'} [L.IsStrictlySupported e]
    (f : K ⟶ L) :
    extendMap (restrictionMap f e) e ≫ (extensionIso e L).hom = (extensionIso e K).hom ≫ f := by
  ext j
  by_cases hj : ∃ i, e.f i = j
  · obtain ⟨i, hi⟩ := hj
    change (extendMap (restrictionMap f e) e).f j ≫ (componentIso e L j).hom =
      (componentIso e K j).hom ≫ f.f j
    rw [componentIso_image e K i j hi, componentIso_image e L i j hi,
      extendMap_f _ e hi, restrictionMap_f' _ e hi]
    simp only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
  · exact ((K.restriction e).isZero_extend_X e j (by simpa using hj)).eq_of_src _ _

def homologyIso (i : ι) : (K.restriction e).homology i ≅ K.homology (e.f i) :=
  ((K.restriction e).extendHomologyIso e rfl).symm ≪≫
    HomologicalComplex.homologyMapIso (extensionIso e K) (e.f i)

theorem quasiIso {L : HomologicalComplex C c'} [L.IsStrictlySupported e]
    (f : K ⟶ L) [QuasiIso f] : QuasiIso (restrictionMap f e) := by
  have : QuasiIso (extendMap (restrictionMap f e) e ≫ (extensionIso e L).hom) := by
    rw [extensionIso_natural]
    infer_instance
  have : QuasiIso (extendMap (restrictionMap f e) e) :=
    quasiIso_of_comp_right _ (extensionIso e L).hom
  exact (quasiIso_extendMap_iff _ e).mp this

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SupportedRestriction
