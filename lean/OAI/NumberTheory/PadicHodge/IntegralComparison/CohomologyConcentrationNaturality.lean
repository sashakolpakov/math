import OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.DualComplexHomology

/-! # Cohomology Concentration Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentrationNaturality

noncomputable section

/-! The canonical zigzag from a complex to its cohomology in one
degree is natural in the original complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false

universe u v

theorem inverse_square {D : Type*} [Category* D] {A B A' B' : D}
    (a : A ⟶ B) (b : A' ⟶ B') (e : A ≅ A') (f : B ≅ B')
    (h : a ≫ f.hom = e.hom ≫ b) : b ≫ f.inv = e.inv ≫ a := by
  apply (cancel_mono f.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

variable {C : Type u} [Category.{v} C] [Abelian C]

open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration

@[reassoc]
theorem zeroCycles_naturality {K L : CochainComplex C ℕ} (a : K ⟶ L) :
    CohomologyConcentration.zeroCyclesMap K ≫ a =
      (CochainComplex.single₀ C).map (HomologicalComplex.cyclesMap a 0) ≫ CohomologyConcentration.zeroCyclesMap L := by
  apply HomologicalComplex.Hom.ext
  funext n
  by_cases hn : n = 0
  · subst n
    simp only [HomologicalComplex.comp_f, CohomologyConcentration.zeroCyclesMap_f_zero, CochainComplex.single₀_map_f_zero]
    exact (HomologicalComplex.cyclesMap_i a 0).symm
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0 (K.cycles 0) n hn).eq_of_src _ _

@[reassoc]
theorem extend_single_inverse_naturality (c : ℕ) {A B : C} (a : A ⟶ B) :
    (HomologicalComplex.single C (.up ℕ) c).map a ≫
        (HomologicalComplex.extendSingleIso (CohomologyConcentration.shift c) B 0 c (by simp [CohomologyConcentration.shift])).inv =
      (HomologicalComplex.extendSingleIso (CohomologyConcentration.shift c) A 0 c (by simp [CohomologyConcentration.shift])).inv ≫
        HomologicalComplex.extendMap ((CochainComplex.single₀ C).map a) (CohomologyConcentration.shift c) := by
  apply HomologicalComplex.Hom.ext
  funext n
  by_cases hn : n = c
  · subst n
    simp only [HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self,
      HomologicalComplex.extendSingleIso_inv_f, HomologicalComplex.extendMap_f _ (CohomologyConcentration.shift c)
        (show (CohomologyConcentration.shift c).f 0 = c by simp [CohomologyConcentration.shift]), Category.assoc,
      Iso.inv_hom_id_assoc]
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℕ) c A n hn).eq_of_src _ _

@[reassoc]
theorem cyclesHomology_naturality {K L : CochainComplex C ℕ} (a : K ⟶ L) (c : ℕ) :
    HomologicalComplex.cyclesMap (HomologicalComplex.truncGE'Map a (CohomologyConcentration.shift c)) 0 ≫
        (CohomologyConcentration.cyclesHomologyIso L c).hom =
      (CohomologyConcentration.cyclesHomologyIso K c).hom ≫ HomologicalComplex.homologyMap a c := by
  let e := CohomologyConcentration.shift c
  have he : e.f 0 = c := by simp [e, CohomologyConcentration.shift]
  let b := HomologicalComplex.truncGE'Map a e
  let t := HomologicalComplex.truncGEMap a e
  let : QuasiIsoAt (CohomologyConcentration.projection K c) c := K.quasiIsoAt_πTruncGE e he
  let : QuasiIsoAt (CohomologyConcentration.projection L c) c := L.quasiIsoAt_πTruncGE e he
  have h₁ := (HomologicalComplex.homologyπ_naturality b 0).symm
  have h₂ := inverse_square (HomologicalComplex.homologyMap t c)
    (HomologicalComplex.homologyMap b 0)
    ((CohomologyConcentration.tail K c).extendHomologyIso e he) ((CohomologyConcentration.tail L c).extendHomologyIso e he)
    (HomologicalComplex.extendHomologyIso_hom_naturality b e he)
  have hπ : HomologicalComplex.homologyMap a c ≫ (isoOfQuasiIsoAt (CohomologyConcentration.projection L c) c).hom =
      (isoOfQuasiIsoAt (CohomologyConcentration.projection K c) c).hom ≫ HomologicalComplex.homologyMap t c := by
    have h := congrArg (fun f => HomologicalComplex.homologyMap f c)
      (HomologicalComplex.πTruncGE_naturality a e).symm
    simpa only [HomologicalComplex.homologyMap_comp, isoOfQuasiIsoAt_hom, CohomologyConcentration.projection, t] using h
  have h₃ := inverse_square _ _ (isoOfQuasiIsoAt (CohomologyConcentration.projection K c) c)
    (isoOfQuasiIsoAt (CohomologyConcentration.projection L c) c) hπ
  have h₂₃ := DualComplexHomology.compose_squares _ _ _ _ _ _ _ h₂ h₃
  simpa only [CohomologyConcentration.cyclesHomologyIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    e, b, CohomologyConcentration.tail, CochainComplex.isoHomologyπ₀, HomologicalComplex.isoHomologyπ_hom] using
    DualComplexHomology.compose_squares _ _ _ _ _ _ _ h₁ h₂₃

@[reassoc]
theorem inclusion_naturality {K L : CochainComplex C ℕ} (a : K ⟶ L) (c : ℕ) :
    (HomologicalComplex.single C (.up ℕ) c).map (HomologicalComplex.homologyMap a c) ≫
        CohomologyConcentration.inclusion L c =
      CohomologyConcentration.inclusion K c ≫ HomologicalComplex.truncGEMap a (CohomologyConcentration.shift c) := by
  let e := CohomologyConcentration.shift c
  let b := HomologicalComplex.truncGE'Map a e
  let S := HomologicalComplex.single C (.up ℕ) c
  have h₁ := DualComplexHomology.map_square S _ _ _ _
    (inverse_square _ _ (CohomologyConcentration.cyclesHomologyIso K c) (CohomologyConcentration.cyclesHomologyIso L c)
      (cyclesHomology_naturality a c))
  have h₂ := extend_single_inverse_naturality c (HomologicalComplex.cyclesMap b 0)
  have h₃ := (DualComplexHomology.map_square (e.extendFunctor C) _ _ _ _
    (zeroCycles_naturality b)).symm
  have h₂₃ := DualComplexHomology.compose_squares _ _ _ _ _ _ _ h₂ h₃
  simpa only [CohomologyConcentration.inclusion, Category.assoc, e, b, S, CohomologyConcentration.tail, HomologicalComplex.truncGEMap,
    ComplexShape.Embedding.extendFunctor] using
    DualComplexHomology.compose_squares _ _ _ _ _ _ _ h₁ h₂₃

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentrationNaturality
