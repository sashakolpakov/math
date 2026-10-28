import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CechSingle
import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.RowTotalNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConcentrationNaturality

/-! # Single Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.SingleNaturality

noncomputable section

/-! The Čech cohomology shift for a sheaf placed in one degree is
natural in the sheaf, including the original signed total flip. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CechSingle OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentrationNaturality

variable {X S : Scheme.{u}} (π : X ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
  {M N : X.Modules} (a : M ⟶ N) (c : ℕ)

def bicomplexMap : CechSingle.bicomplex π U M c ⟶ CechSingle.bicomplex π U N c :=
  QuasiIso.bicomplexMap π U ((HomologicalComplex.single X.Modules (.up ℕ) c).map a)

@[reassoc]
theorem row_naturality : (bicomplexMap π U a c).f c ≫ (CechSingle.rowIso π U N c).hom =
    (CechSingle.rowIso π U M c).hom ≫ (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).map a := by
  let F := AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U
  change F.map (((HomologicalComplex.single X.Modules (.up ℕ) c).map a).f c) ≫
      F.map (HomologicalComplex.singleObjXSelf (.up ℕ) c N).hom =
    F.map (HomologicalComplex.singleObjXSelf (.up ℕ) c M).hom ≫ F.map a
  rw [← F.map_comp, ← F.map_comp]
  congr 1
  simp only [HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id, Category.comp_id]

@[reassoc]
theorem homology_naturality (n : ℕ) :
    HomologicalComplex.homologyMap (QuasiIso.map π U
      ((HomologicalComplex.single X.Modules (.up ℕ) c).map a)) (n + c) ≫ (CechSingle.homologyIso π U N c n).hom =
      (CechSingle.homologyIso π U M c n).hom ≫ HomologicalComplex.homologyMap
        ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).map a) n := by
  let b := bicomplexMap π U a c
  let bf := GeometricComparison.TotalFlip.TotalFlipNaturality.flipped b
  have hf := congrArg (fun f => HomologicalComplex.homologyMap f (n + c))
    (GeometricComparison.TotalFlip.TotalFlipNaturality.natural b)
  simp only [HomologicalComplex.homologyMap_comp] at hf
  have hfi := CohomologyConcentrationNaturality.inverse_square _ _
    (HomologicalComplex.homologyMapIso ((CechSingle.bicomplex π U M c).totalFlipIso (.up ℕ)) (n + c))
    (HomologicalComplex.homologyMapIso ((CechSingle.bicomplex π U N c).totalFlipIso (.up ℕ)) (n + c)) hf
  have hs : HomologicalComplex.homologyMap (HomologicalComplex₂.total.map bf (.up ℕ)) (n + c) ≫
        (Single.RowTotal.homologyIso (CechSingle.bicomplex π U N c).flip c (CechSingle.off_degree π U N c) n).hom =
      (Single.RowTotal.homologyIso (CechSingle.bicomplex π U M c).flip c (CechSingle.off_degree π U M c) n).hom ≫
        HomologicalComplex.homologyMap (b.f c) n :=
    Single.RowTotalNaturality.homology_naturality bf c (CechSingle.off_degree π U M c) (CechSingle.off_degree π U N c) n
  have hr := congrArg (fun f => HomologicalComplex.homologyMap f n) (row_naturality π U a c)
  simp only [HomologicalComplex.homologyMap_comp] at hr
  have hsr := DualComplexHomology.compose_squares _ _ _ _ _ _ _ hs hr
  simpa only [CechSingle.homologyIso, Iso.trans_hom, Iso.symm_hom, HomologicalComplex.homologyMapIso_hom,
    Category.assoc, b, bf, bicomplexMap, QuasiIso.map] using
    DualComplexHomology.compose_squares _ _ _ _ _ _ _ hfi hsr

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.SingleNaturality
