import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappingConeContractions

/-! # Mapping Cone Top Term -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappingConeTopTerm

noncomputable section

/-! At a vanishing next source term, the last term of a mapping cone is
its target term. Its incoming map has the usual two-component formula. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CochainComplex
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {K L : CochainComplex C ℤ}

def mappingConeTopProjectionIso (φ : K ⟶ L) (hK : IsZero (K.X 1)) :
    (mappingCone φ).X 0 ≅ L.X 0 where
  hom := (mappingCone.snd φ).v 0 0 (by decide)
  inv := (mappingCone.inr φ).f 0
  hom_inv_id := by
    have hz : (mappingCone.fst φ).1.v 0 1 (by decide) = 0 := hK.eq_of_tgt _ _
    simpa only [hz, zero_comp, zero_add] using mappingCone.id_X φ 0 1 (by decide)
  inv_hom_id := mappingCone.inr_f_snd_v φ 0

theorem mappingCone_d_topProjection (φ : K ⟶ L) (hK : IsZero (K.X 1)) :
    (mappingCone φ).d (-1) 0 ≫ (mappingConeTopProjectionIso φ hK).hom =
      (mappingCone.fst φ).1.v (-1) 0 (by decide) ≫ φ.f 0 +
        (mappingCone.snd φ).v (-1) (-1) (by decide) ≫ L.d (-1) 0 :=
  mappingCone.d_snd_v φ (-1) 0 (by decide)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappingConeTopTerm
