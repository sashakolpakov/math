import Mathlib.Algebra.Homology.ShortComplex.Preadditive

/-! # Zero Complex Homology Map -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ZeroComplexHomologyMap.Construction.LocalSectionLifting

noncomputable section

/-! For complexes with zero differentials, injectivity on homology is injectivity of the middle map. -/

open _root_.CategoryTheory

variable {C : Type*} [Category* C] [Preadditive C]
    {S T : ShortComplex C} [S.HasHomology] [T.HasHomology]

theorem zeroShortComplex_middle_mono (φ : S ⟶ T)
    (hfS : S.f = 0) (hgS : S.g = 0) (hfT : T.f = 0) (hgT : T.g = 0)
    [Mono (ShortComplex.homologyMap φ)] : Mono φ.τ₂ := by
  let D := ShortComplex.LeftHomologyMapData.ofZeros φ hfS hgS hfT hgT
  let eS : S.homology ≅ S.X₂ := (ShortComplex.LeftHomologyData.ofZeros S hfS hgS).homologyIso
  let eT : T.homology ≅ T.X₂ := (ShortComplex.LeftHomologyData.ofZeros T hfT hgT).homologyIso
  have he : φ.τ₂ = eS.inv ≫ ShortComplex.homologyMap φ ≫ eT.hom := by
    rw [D.homologyMap_eq]
    change φ.τ₂ = eS.inv ≫ (eS.hom ≫ φ.τ₂ ≫ eT.inv) ≫ eT.hom
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [he]
  infer_instance

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ZeroComplexHomologyMap.Construction.LocalSectionLifting
