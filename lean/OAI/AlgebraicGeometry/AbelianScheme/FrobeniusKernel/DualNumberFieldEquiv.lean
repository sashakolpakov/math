import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks

/-! # Dual Number Field Equiv -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualNumberFieldEquiv.Construction

noncomputable section

/-!
Field isomorphisms transport the actual dual-number tests, including
their origin and scalar maps. These comparisons are the infinitesimal
input for transporting CMPoints Lie ranks to the fixed geometric field.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks

variable {k l : Type u} [Field k] [Field l] (e : k ≃+* l)

def dualNumberFieldEquiv : DualNumber k ≃+* DualNumber l where
  toFun x := ⟨e x.fst, e x.snd⟩
  invFun x := ⟨e.symm x.fst, e.symm x.snd⟩
  left_inv x := by ext <;> exact e.symm_apply_apply _
  right_inv x := by ext <;> exact e.apply_symm_apply _
  map_add' x y := by ext <;> exact e.map_add _ _
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · exact e.map_mul _ _
    · change e (x.fst * y.snd + x.snd * y.fst) =
        e x.fst * e y.snd + e x.snd * e y.fst
      rw [map_add, map_mul, map_mul]

theorem dualNumberFieldEquiv_scale (a : k) (z : DualNumber k) :
    dualNumberFieldEquiv e (AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale k a z) =
      AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale l (e a) (dualNumberFieldEquiv e z) := by
  apply TrivSqZeroExt.ext
  · change e ((AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale k a z).fst) =
      (AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale l (e a) (dualNumberFieldEquiv e z)).fst
    simp only [AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale, TrivSqZeroExt.fst_map]
    rfl
  · change e ((AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale k a z).snd) =
      (AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale l (e a) (dualNumberFieldEquiv e z)).snd
    simp only [AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale, TrivSqZeroExt.snd_map, LinearMap.smul_apply, LinearMap.id_apply]
    change e (a * z.snd) = e a * e z.snd
    exact e.map_mul _ _

def fieldPointBaseIso :
    (Over.map (Spec.map e.toCommRingCatIso.hom)).obj (Over.mk (𝟙 (Spec (.of l)))) ≅
      Over.mk (𝟙 (Spec (.of k))) :=
  Over.isoMk (Scheme.Spec.mapIso e.toCommRingCatIso.op) (by
    change Spec.map e.toCommRingCatIso.hom ≫ 𝟙 _ = 𝟙 _ ≫ Spec.map e.toCommRingCatIso.hom
    rw [Category.comp_id, Category.id_comp])

/-- The native dual-number test over l, regarded over k, is the
original dual-number test over k through the field isomorphism. -/
def dualNumberTestFieldIso :
    (Over.map (Spec.map e.toCommRingCatIso.hom)).obj (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest l) ≅ AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k :=
  Over.isoMk (Scheme.Spec.mapIso (dualNumberFieldEquiv e).toCommRingCatIso.op) (by
    change Spec.map (dualNumberFieldEquiv e).toCommRingCatIso.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) =
      Spec.map (CommRingCat.ofHom (algebraMap l (DualNumber l))) ≫ Spec.map e.toCommRingCatIso.hom
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    apply TrivSqZeroExt.ext
    · rfl
    · exact e.map_zero)

theorem dualNumberTestFieldIso_origin :
    (Over.map (Spec.map e.toCommRingCatIso.hom)).map (AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin l) ≫
      (dualNumberTestFieldIso e).hom = (fieldPointBaseIso e).hom ≫ AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction l)) ≫
      Spec.map (dualNumberFieldEquiv e).toCommRingCatIso.hom =
    Spec.map e.toCommRingCatIso.hom ≫ Spec.map (CommRingCat.ofHom (AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction k))
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem dualNumberTestFieldIso_scalar (a : k) :
    (Over.map (Spec.map e.toCommRingCatIso.hom)).map (AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar l (e a)) ≫
      (dualNumberTestFieldIso e).hom =
    (dualNumberTestFieldIso e).hom ≫ AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar k a := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale l (e a)).toRingHom) ≫
      Spec.map (dualNumberFieldEquiv e).toCommRingCatIso.hom =
    Spec.map (dualNumberFieldEquiv e).toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom (AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale k a).toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun z => (dualNumberFieldEquiv_scale e a z).symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualNumberFieldEquiv.Construction
