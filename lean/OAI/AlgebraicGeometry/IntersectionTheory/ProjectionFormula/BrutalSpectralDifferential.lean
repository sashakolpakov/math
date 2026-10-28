import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalConnectingMap
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.ConnectingHomology
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.SpectralConnecting
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalTensorSpectralSequence

/-! # Brutal Spectral Differential -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalSpectralDifferential

noncomputable section

/-! The connecting differential of the tail-filtration spectral object
is the tensor of the adjacent-column cocycle, through canonical relative
homology isomorphisms. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CochainComplex _root_.CochainComplex.HomComplex

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalFiltration OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalFiltrationQuotient

abbrev arrow (p : ℤ) : (p : EInt) ⟶ ((p + 1 : ℤ) : EInt) :=
  homOfLE (WithBotTop.coe_le_coe.mpr (by omega))

variable (R : Type) [CommRing R] (A K : CochainComplex (ModuleCat.{0} R) ℤ)

@[reassoc]
theorem relative_δ (p n m : ℤ) (h : n + 1 = m) :
    (Tensor.SpectralObject.abelian R K (BrutalFiltration.filtration R A)).δ (arrow p) (arrow (p + 1)) n m h ≫
      (BrutalFiltrationQuotient.relativeTermIso R A p K m).hom =
    (BrutalFiltrationQuotient.relativeTermIso R A (p + 1) K n).hom ≫
      CocycleHomology.map R
        (Tensor.Cochain.mapCocycle R K (BrutalConnectingMap.columnConnecting R A p)) n m (by omega) := by
  simp only [BrutalFiltrationQuotient.relativeTermIso, Iso.trans_hom, BrutalFiltrationQuotient.tensorConeHomologyIso_hom]
  rw [← Category.assoc, Tensor.SpectralConnecting.abelian_δ]
  simp only [Category.assoc]
  congr 1
  change (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (.up ℤ) 0).shiftMap
      (ShiftedHom.map (mappingConeCompTriangle (BrutalFiltrationQuotient.stageMap R A p) (BrutalFiltrationQuotient.stageMap R A (p + 1))).mor₃
        (Tensor.Homotopy.complexFunctor R K)) n m (by omega) ≫
      HomologicalComplex.homologyMap ((Tensor.Homotopy.complexFunctor R K).map
        (mappingCone.descShortComplex (BrutalFiltrationQuotient.sequence R A p))) m =
    HomologicalComplex.homologyMap ((Tensor.Homotopy.complexFunctor R K).map
        (mappingCone.descShortComplex (BrutalFiltrationQuotient.sequence R A (p + 1)))) n ≫ _
  rw [Tensor.ConnectingHomology.comp_triangle, Category.assoc,
    ← HomologicalComplex.homologyMap_comp, ← CategoryTheory.Functor.map_comp]
  change CocycleHomology.map R
      (Tensor.Cochain.mapCocycle R K (-mappingCone.fst (BrutalFiltrationQuotient.sequence R A (p + 1)).f)) n m (by omega) ≫
    HomologicalComplex.homologyMap ((Tensor.Homotopy.complexFunctor R K).map
      (mappingCone.inr (BrutalFiltrationQuotient.sequence R A p).f ≫ mappingCone.descShortComplex (BrutalFiltrationQuotient.sequence R A p))) m = _
  rw [mappingCone.inr_descShortComplex,
    Tensor.ConnectingHomology.connecting R (BrutalFiltrationQuotient.sequence R A (p + 1)) (BrutalFiltrationQuotient.splitting R A (p + 1)) K,
    Category.assoc]
  congr 1
  rw [← CocycleHomology.postcomp, ← Tensor.ConnectingHomology.mapCocycle_postcomp]
  rfl

@[reassoc]
theorem firstPage_d (p q : ℤ) :
    ((BrutalTensorSpectralSequence.spectralSequence R A K).page 2).d (p, q + 1) (p + 2, q) ≫
      (BrutalTensorSpectralSequence.firstPageXIso R A K (p + 2) q).hom =
    (BrutalTensorSpectralSequence.firstPageXIso R A K p (q + 1)).hom ≫
      CocycleHomology.map R
        (Tensor.Cochain.mapCocycle R K (BrutalConnectingMap.columnConnecting R A q))
        (p + (q + 1)) ((p + 2) + q) (by omega) := by
  let X := Tensor.SpectralObject.abelian R K (BrutalFiltration.filtration R A)
  have hpq : (ComplexShape.up' (⟨2, 1 - 2⟩ : ℤ × ℤ)).Rel (p, q + 1) (p + 2, q) := by
    change (p + 2, (q + 1) + (1 - 2)) = (p + 2, q)
    congr 1
    omega
  have hd := X.spectralSequence_first_page_d_eq Abelian.SpectralObject.coreE₂Cohomological
    (p, q + 1) (p + 2, q) hpq (q : EInt) ((q + 1 : ℤ) : EInt) (((q + 1) + 1 : ℤ) : EInt)
    rfl rfl rfl (p + (q + 1)) ((p + 2) + q) rfl (by omega)
  change ((X.spectralSequence Abelian.SpectralObject.coreE₂Cohomological).page 2).d
    (p, q + 1) (p + 2, q) ≫ _ = _
  rw [hd]
  simp only [BrutalTensorSpectralSequence.firstPageXIso, Iso.trans_hom, Category.assoc]
  change _ ≫ X.δ (arrow q) (arrow (q + 1)) (p + (q + 1)) ((p + 2) + q) (by omega) ≫
    (X.spectralSequenceFirstPageXIso Abelian.SpectralObject.coreE₂Cohomological
      (p + 2, q) (q : EInt) ((q + 1 : ℤ) : EInt) rfl rfl ((p + 2) + q) rfl).inv ≫
    (X.spectralSequenceFirstPageXIso Abelian.SpectralObject.coreE₂Cohomological
      (p + 2, q) (q : EInt) ((q + 1 : ℤ) : EInt) rfl rfl ((p + 2) + q) rfl).hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc]
  rw [relative_δ]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalSpectralDifferential
