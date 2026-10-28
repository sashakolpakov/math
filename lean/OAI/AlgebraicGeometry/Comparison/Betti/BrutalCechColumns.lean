import OAI.AlgebraicGeometry.Comparison.Betti.BrutalCechAcyclicity
import OAI.AlgebraicGeometry.Comparison.Betti.Cech.Column
import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveTotalColumn

/-! # Brutal Cech Columns -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.BrutalCechColumns.Hodge

noncomputable section

section

/-! Čech columns of the independent Hodge truncation are the retained original columns or zero columns. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration OAI.AlgebraicGeometry.Comparison.Betti.Cech.Column

variable {X : TopCat.{0}} {ι : Type} (U : ι → Opens X)
  (K : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℕ) (r : ℤ) (q : ℕ)

theorem brutalCechInclusionColumn_isIso (h : r ≤ (q : ℤ)) :
    IsIso ((Cech.Row.additiveSheafSectionCechBicomplexMap U
      (Godement.AdditiveImage.additiveGodementComplexMap (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r))).f q) := by
  have hK : IsIso ((Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r).f q) := by
    change IsIso (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K r q)
    rw [← BrutalComplexMap.Hodge.brutalRetainedTermIso_inclusion K r q h]
    infer_instance
  let e : (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r).X q ≅ K.X q := @asIso _ _ _ _ ((Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r).f q) hK
  have hF : IsIso ((Godement.AdditiveImage.additiveGodementComplexMap (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r)).f q) :=
    ((Complex.SheafForget.Flasque.sheafForget X).mapIso e).isIso_hom
  exact Cech.Column.cechColumnMap_isIso U (Godement.AdditiveImage.additiveGodementComplexMap (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r)) q

theorem brutalCechColumn_isZero (h : ¬ r ≤ (q : ℤ)) :
    IsZero ((FlasqueCechTotal.additiveSheafSectionCechBicomplex U (Godement.Cech.additiveGodementComplex (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r))).X q) :=
  Cech.Column.cechColumn_isZero U (Godement.Cech.additiveGodementComplex (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r)) q
    ((Complex.SheafForget.Flasque.sheafForget X).map_isZero (BrutalComplexMap.Hodge.brutalTerm_isZero K r q h))

end

/-! Original coefficient quasi-isomorphisms on Čech columns persist for every independent Hodge truncation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.HomologicalComplex₂

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration OAI.AlgebraicGeometry.Comparison.Betti.Cech.Column

variable {X Y : TopCat.{0}} (f : Y ⟶ X) {ι : Type} (U : ι → Opens X)
  {K : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℕ}
  {L : CochainComplex (ConstantSheafSections.ComplexSheaves Y) ℕ}
  (α : K ⟶ ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℕ)).obj L) (r : ℤ)

def brutalCechPullbackBicomplexMap :=
  Sheaf.CechPullbackTotal.sheafCechPullbackBicomplexMap f U (Godement.AdditiveImage.additiveDirectImageComplexMap f (BrutalCechAcyclicity.Hodge.brutalSheafDirectImageMap f α r))

theorem brutalCechPullbackColumn_quasiIso (q : ℕ)
    (hα : QuasiIso ((Sheaf.CechPullbackTotal.sheafCechPullbackBicomplexMap f U (Godement.AdditiveImage.additiveDirectImageComplexMap f α)).f q)) :
    QuasiIso ((brutalCechPullbackBicomplexMap f U α r).f q) := by
  let V := fun i => (Opens.map f).obj (U i)
  let jK := Cech.Row.additiveSheafSectionCechBicomplexMap U (Godement.AdditiveImage.additiveGodementComplexMap (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r))
  let jL := Cech.Row.additiveSheafSectionCechBicomplexMap V (Godement.AdditiveImage.additiveGodementComplexMap (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r))
  by_cases h : r ≤ (q : ℤ)
  · have hK : IsIso (jK.f q) := brutalCechInclusionColumn_isIso U K r q h
    have hL : IsIso (jL.f q) := brutalCechInclusionColumn_isIso V L r q h
    have hs := congrArg (fun φ => φ.f q)
      (Cech.Column.sheafCechPullbackBicomplexMap_coefficientSquare (U := U) (f := f)
        (Godement.AdditiveImage.additiveDirectImageComplexMap f (BrutalCechAcyclicity.Hodge.brutalSheafDirectImageMap f α r))
        (Godement.AdditiveImage.additiveDirectImageComplexMap f α) (Godement.AdditiveImage.additiveGodementComplexMap (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r))
        (Godement.AdditiveImage.additiveGodementComplexMap (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r)) (BrutalCechAcyclicity.Hodge.brutalSheafDirectImageMap_additiveInclusion f α r))
    change jK.f q ≫ (Sheaf.CechPullbackTotal.sheafCechPullbackBicomplexMap f U (Godement.AdditiveImage.additiveDirectImageComplexMap f α)).f q =
      (brutalCechPullbackBicomplexMap f U α r).f q ≫ jL.f q at hs
    have hc : QuasiIso ((brutalCechPullbackBicomplexMap f U α r).f q ≫ jL.f q) := by
      erw [← hs]
      exact quasiIso_comp _ _ (hφ := quasiIso_of_isIso (jK.f q)) (hφ' := hα)
    exact quasiIso_of_comp_right _ _ (hφ := quasiIso_of_isIso (jL.f q)) (hφφ' := hc)
  · let BK := FlasqueCechTotal.additiveSheafSectionCechBicomplex U (Godement.Cech.additiveGodementComplex (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r))
    let BL := FlasqueCechTotal.additiveSheafSectionCechBicomplex V (Godement.Cech.additiveGodementComplex (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal L r))
    have hK : IsZero (BK.X q) := brutalCechColumn_isZero U K r q h
    have hL : IsZero (BL.X q) := brutalCechColumn_isZero V L r q h
    let e : BK.X q ≅ BL.X q :=
      { hom := (brutalCechPullbackBicomplexMap f U α r).f q
        inv := 0
        hom_inv_id := hK.eq_of_src _ _
        inv_hom_id := hL.eq_of_src _ _ }
    have hE : IsIso e.hom := e.isIso_hom
    exact quasiIso_of_isIso e.hom

theorem brutalCechPullbackTotal_quasiIso
    (hα : ∀ q, QuasiIso ((Sheaf.CechPullbackTotal.sheafCechPullbackBicomplexMap f U (Godement.AdditiveImage.additiveDirectImageComplexMap f α)).f q)) :
    QuasiIso (Sheaf.CechPullbackTotal.sheafCechPullbackTotalMap f U
      (Godement.AdditiveImage.additiveDirectImageComplexMap f (BrutalCechAcyclicity.Hodge.brutalSheafDirectImageMap f α r))) :=
  AdditiveTotalColumn.additive_total_map_quasiIso_of_columns (brutalCechPullbackBicomplexMap f U α r)
    (fun q => brutalCechPullbackColumn_quasiIso f U α r q (hα q))

end

end OAI.AlgebraicGeometry.Comparison.Betti.BrutalCechColumns.Hodge
