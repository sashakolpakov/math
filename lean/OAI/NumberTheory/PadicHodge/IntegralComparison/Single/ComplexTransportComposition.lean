import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ComplexTransport

/-! # Complex Transport Composition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ComplexTransportComposition

noncomputable section

/-! Composition of actual augmentation transport through naturally isomorphic functors. -/

open _root_.CategoryTheory

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) [F.Additive] [G.Additive] [H.Additive]
  (e : F ⋙ G ≅ H) {Z : C} {Z' : D} {Z'' : E}
  (eF : F.obj Z ≅ Z') (eG : G.obj Z' ≅ Z'') (eH : H.obj Z ≅ Z'')
  (he : G.map eF.hom ≫ eG.hom = (e.app Z).hom ≫ eH.hom)

include he

omit [Abelian C] [Abelian D] [Abelian E] [F.Additive] [G.Additive] [H.Additive] in
theorem inverse : eG.inv ≫ G.map eF.inv ≫ (e.app Z).hom = eH.inv := by
  apply (cancel_mono eH.hom).mp
  rw [Category.assoc, Category.assoc, ← he, ← Category.assoc (G.map eF.inv), ← G.map_comp,
    eF.inv_hom_id, G.map_id, Category.id_comp, eG.inv_hom_id, eH.inv_hom_id]

variable {K : CochainComplex C ℕ} (ι : (CochainComplex.single₀ C).obj Z ⟶ K)

theorem map : ComplexTransport.map G eG (ComplexTransport.map F eF ι) ≫
    ((NatIso.mapHomologicalComplex e (.up ℕ)).app K).hom = ComplexTransport.map H eH ι := by
  apply HomologicalComplex.from_single_hom_ext
  change (ComplexTransport.map G eG (ComplexTransport.map F eF ι)).f 0 ≫
    (e.app (K.X 0)).hom = (ComplexTransport.map H eH ι).f 0
  rw [ComplexTransport.map_zero, ComplexTransport.map_zero,
    ComplexTransport.map_zero]
  let b : Z ⟶ K.X 0 := ι.f 0
  change (eG.inv ≫ G.map (eF.inv ≫ F.map b)) ≫ (e.app (K.X 0)).hom = eH.inv ≫ H.map b
  rw [G.map_comp]
  have hnat : G.map (F.map b) ≫ (e.app (K.X 0)).hom = (e.app Z).hom ≫ H.map b :=
    e.hom.naturality b
  rw [Category.assoc, Category.assoc, hnat, ← Category.assoc (G.map eF.inv),
    ← Category.assoc, inverse F G H e eF eG eH he]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ComplexTransportComposition
