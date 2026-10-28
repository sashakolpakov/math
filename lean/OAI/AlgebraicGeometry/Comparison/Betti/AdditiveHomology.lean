import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Additive Homology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AdditiveHomology.Cech

noncomputable section

section

/-! Compute additive homology from a surjective coefficient map on cycles. -/

open _root_.CategoryTheory

def additiveHomologyCoefficientIso (S : ShortComplex AddCommGrpCat)
    {V : Type} [AddCommGroup V] (f : S.g.hom.ker →+ V)
    (hf : Function.Surjective f) (hker : S.abToCycles.range = f.ker) :
    S.homology ≅ AddCommGrpCat.of V :=
  S.abHomologyIso ≪≫
    ((QuotientAddGroup.quotientAddEquivOfEq hker).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective f hf)).toAddCommGrpIso

theorem additiveHomologyCoefficientIso_quotient (S : ShortComplex AddCommGrpCat)
    {V : Type} [AddCommGroup V] (f : S.g.hom.ker →+ V)
    (hf : Function.Surjective f) (hker : S.abToCycles.range = f.ker) (z : S.g.hom.ker) :
    (additiveHomologyCoefficientIso S f hf hker).hom
      (S.abHomologyIso.inv (QuotientAddGroup.mk z)) = f z := by
  change ((QuotientAddGroup.quotientAddEquivOfEq hker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective f hf))
      (S.abHomologyIso.hom (S.abHomologyIso.inv (QuotientAddGroup.mk z))) = f z
  rw [Iso.inv_hom_id_apply]
  rfl

end

section

/-! Normalize the coefficient isomorphism on the actual categorical cycle projection. -/

open _root_.CategoryTheory

theorem additiveHomologyCoefficientIso_homologyπ (S : ShortComplex AddCommGrpCat)
    {V : Type} [AddCommGroup V] (f : S.g.hom.ker →+ V)
    (hf : Function.Surjective f) (hker : S.abToCycles.range = f.ker) :
    S.homologyπ ≫ (additiveHomologyCoefficientIso S f hf hker).hom =
      S.abCyclesIso.hom ≫ AddCommGrpCat.ofHom f := by
  have hπ : S.homologyπ ≫ S.abHomologyIso.hom =
      S.abCyclesIso.hom ≫ AddCommGrpCat.ofHom (QuotientAddGroup.mk' S.abToCycles.range) :=
    S.abLeftHomologyData.homologyπ_comp_homologyIso_hom
  change S.homologyπ ≫ (S.abHomologyIso.hom ≫ _) = _
  rw [← Category.assoc, hπ, Category.assoc]
  congr 1

theorem additiveCyclesIso_hom_value (S : ShortComplex AddCommGrpCat) (z : S.cycles) :
    (S.abCyclesIso.hom z).val = S.iCycles z := by
  exact ConcreteCategory.congr_hom S.abLeftHomologyData.cyclesIso_hom_comp_i z

end

/-! Degree-zero comparison is determined by the actual map on kernels of the first differential. -/

open _root_.CategoryTheory _root_.HomologicalComplex

variable (K L : CochainComplex AddCommGrpCat ℕ)

def additiveZeroCyclesIso : K.cycles 0 ≅ AddCommGrpCat.of (K.d 0 1).hom.ker :=
  K.cyclesIsoSc' 0 0 1 (by simp) (by simp) ≪≫ (K.sc' 0 0 1).abCyclesIso

theorem additiveZeroCyclesIso_value (z : K.cycles 0) :
    ((additiveZeroCyclesIso K).hom z).val = K.iCycles 0 z := by
  exact (additiveCyclesIso_hom_value (K.sc' 0 0 1)
    ((K.cyclesIsoSc' 0 0 1 (by simp) (by simp)).hom z)).trans
      (ConcreteCategory.congr_hom (K.cyclesIsoSc'_hom_iCycles 0 0 1 (by simp) (by simp)) z)

def additiveHZeroCyclesIso : K.homology 0 ≅ AddCommGrpCat.of (K.d 0 1).hom.ker :=
  (K.isoHomologyπ 0 0 (by simp) (by simp)).symm ≪≫ additiveZeroCyclesIso K

theorem additiveHZeroCyclesIso_homologyπ :
    K.homologyπ 0 ≫ (additiveHZeroCyclesIso K).hom = (additiveZeroCyclesIso K).hom := by
  exact Iso.hom_inv_id_assoc (K.isoHomologyπ 0 0 (by simp) (by simp)) _

variable {K L}

def additiveZeroCycleMap (f : K ⟶ L) : (K.d 0 1).hom.ker →+ (L.d 0 1).hom.ker where
  toFun z := ⟨f.f 0 z.val, by
    have h := ConcreteCategory.congr_hom (f.comm 0 1) z.val
    exact h.trans ((congrArg (f.f 1) z.property).trans (map_zero (f.f 1).hom))⟩
  map_zero' := Subtype.ext (map_zero (f.f 0).hom)
  map_add' z w := Subtype.ext (map_add (f.f 0).hom z.val w.val)

theorem additiveZeroCyclesIso_naturality (f : K ⟶ L) :
    (additiveZeroCyclesIso K).hom ≫ AddCommGrpCat.ofHom (additiveZeroCycleMap f) =
      cyclesMap f 0 ≫ (additiveZeroCyclesIso L).hom := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  apply Subtype.ext
  change f.f 0 ((additiveZeroCyclesIso K).hom z).val =
    ((additiveZeroCyclesIso L).hom (cyclesMap f 0 z)).val
  rw [additiveZeroCyclesIso_value, additiveZeroCyclesIso_value]
  exact (ConcreteCategory.congr_hom (cyclesMap_i f 0) z).symm

theorem additiveHZeroCyclesIso_naturality (f : K ⟶ L) :
    (additiveHZeroCyclesIso K).hom ≫ AddCommGrpCat.ofHom (additiveZeroCycleMap f) =
      homologyMap f 0 ≫ (additiveHZeroCyclesIso L).hom := by
  apply (cancel_epi (K.homologyπ 0)).mp
  rw [← Category.assoc, additiveHZeroCyclesIso_homologyπ, ← Category.assoc,
    homologyπ_naturality, Category.assoc, additiveHZeroCyclesIso_homologyπ]
  exact additiveZeroCyclesIso_naturality f

theorem additiveHZeroMap_isIso_of_zeroCycles (f : K ⟶ L) (hf : Function.Bijective (additiveZeroCycleMap f)) :
    IsIso (homologyMap f 0) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have hK := ConcreteCategory.bijective_of_isIso (additiveHZeroCyclesIso K).hom
  have hL := ConcreteCategory.bijective_of_isIso (additiveHZeroCyclesIso L).hom
  have hc : (fun x => (additiveHZeroCyclesIso L).hom (homologyMap f 0 x)) =
      (fun x => additiveZeroCycleMap f ((additiveHZeroCyclesIso K).hom x)) := by
    funext x
    exact (ConcreteCategory.congr_hom (additiveHZeroCyclesIso_naturality f) x).symm
  have hb : Function.Bijective (fun x => (additiveHZeroCyclesIso L).hom (homologyMap f 0 x)) :=
    hc ▸ hf.comp hK
  constructor
  · intro x y h
    exact hb.injective (congrArg (additiveHZeroCyclesIso L).hom h)
  · intro y
    obtain ⟨x, hx⟩ := hb.surjective ((additiveHZeroCyclesIso L).hom y)
    exact ⟨x, hL.injective hx⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.AdditiveHomology.Cech
