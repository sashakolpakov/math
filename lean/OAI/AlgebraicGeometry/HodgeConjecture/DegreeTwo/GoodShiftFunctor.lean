import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftCohomology

/-! # Good Shift Functor -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions

noncomputable section

/-! Good shifts commute with additive functors preserving the actual boundary cokernel. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
variable (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℕ) (k : ℕ)
variable (hF : ∀ n, (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k).BoundaryGE n →
  F.PreservesRightHomologyOf (K.sc (k+n)))

abbrev functorCochainComplex := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K

def goodShiftFunctorDegreeIso (n : ℕ) :
    ((functorCochainComplex F K).truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).X n ≅
      F.obj ((K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).X n) := by
  by_cases hn : (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k).BoundaryGE n
  · have := hF n hn
    exact (functorCochainComplex F K).truncGE'XIsoOpcycles (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k) rfl hn ≪≫
      (K.sc (k+n)).mapOpcyclesIso F ≪≫
        F.mapIso (K.truncGE'XIsoOpcycles (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k) rfl hn).symm
  · exact (functorCochainComplex F K).truncGE'XIso (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k) rfl hn ≪≫
      F.mapIso (K.truncGE'XIso (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k) rfl hn).symm

theorem goodShiftFunctorDegreeIso_projection (n : ℕ) :
    ((functorCochainComplex F K).restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).f n ≫
        (goodShiftFunctorDegreeIso F K k hF n).hom =
      F.map ((K.restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).f n) := by
  by_cases hn : (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k).BoundaryGE n
  · have := hF n hn
    rw [(functorCochainComplex F K).restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv
      (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k) rfl hn,
      K.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k) rfl hn]
    simp only [goodShiftFunctorDegreeIso, dite_eq_left hn, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Category.assoc, Iso.inv_hom_id_assoc,
      HomologicalComplex.restrictionXIso, eqToIso_refl, Iso.refl_hom, Category.id_comp,
      Functor.map_comp]
    have hp : (functorCochainComplex F K).pOpcycles (k+n) ≫
        ((K.sc (k+n)).mapOpcyclesIso F).hom = F.map (K.pOpcycles (k+n)) :=
      (K.sc (k+n)).rightHomologyData.map F |>.pOpcycles_comp_opcyclesIso_hom
    rw [← Category.assoc]
    exact congrArg (fun q => q ≫ F.map
      (K.truncGE'XIsoOpcycles (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k) rfl hn).inv) hp
  · rw [(functorCochainComplex F K).restrictionToTruncGE'_f_eq_iso_hom_iso_inv
      (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k) rfl hn,
      K.restrictionToTruncGE'_f_eq_iso_hom_iso_inv (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k) rfl hn]
    simp only [goodShiftFunctorDegreeIso, dite_eq_right hn, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Iso.inv_hom_id_assoc,
      HomologicalComplex.restrictionXIso, eqToIso_refl, Iso.refl_hom, Category.id_comp]

def goodShiftFunctorIso :
    (functorCochainComplex F K).truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k) ≅
      (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) := by
  refine HomologicalComplex.Hom.isoOfComponents (goodShiftFunctorDegreeIso F K k hF) ?_
  intro i j hij
  let t := (functorCochainComplex F K).restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)
  apply (cancel_epi (t.f i)).mp
  rw [← Category.assoc, goodShiftFunctorDegreeIso_projection]
  rw [t.comm_assoc i j, goodShiftFunctorDegreeIso_projection]
  change F.map ((K.restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).f i) ≫
      F.map ((K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).d i j) =
    F.map ((K.restriction (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).d i j) ≫
      F.map ((K.restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).f j)
  rw [← Functor.map_comp, ← Functor.map_comp,
    (K.restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).comm i j]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions
