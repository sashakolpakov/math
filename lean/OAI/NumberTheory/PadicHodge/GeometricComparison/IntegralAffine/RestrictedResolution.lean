import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FlasqueVanishing
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.FormExtVanishing
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.ChartExtVanishing
import OAI.NumberTheory.PadicHodge.GeometricComparison.OpenForms
import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.AcyclicResolutionSections

/-! # Restricted Resolution -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.RestrictedResolution.IntegralAffineRestrictedResolution

noncomputable section

/-! Restricting an actual injective resolution to an integral affine open gives an exact positive-degree section complex. -/

open _root_.CategoryTheory Abelian Limits _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] [Module.Flat ℤ R]
  {X Y : Over (Spec (CommRingCat.of R))} (f : Y ⟶ X)
  [IsOpenImmersion f.left] [IsAffine Y.left]

local instance : HasExt.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) := HasExt.standard _

omit [IsAffine Y.left] in
theorem exact_succ (F : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) (I : InjectiveResolution F)
    (hF : ∀ q, Subsingleton (Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y)
      ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f.left).obj F) (q + 1)))
    (n : ℕ) :
    ((((AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f.left) ⋙
      Affine.ChartExtVanishing.AffineChartExtVanishing.sections R Y).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).ExactAt (n + 1) := by
  let G := AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f.left
  let K := (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let e : G.obj F ⟶ K.X 0 := G.map (I.ι.f 0)
  have w : e ≫ K.d 0 1 = 0 := by
    change G.map (I.ι.f 0) ≫ G.map (I.cocomplex.d 0 1) = 0
    rw [← G.map_comp, I.ι_f_zero_comp_complex_d, G.map_zero]
  have : Mono e := G.map_mono (I.ι.f 0)
  have haug : (ShortComplex.mk e (K.d 0 1) w).Exact := I.exact₀.map G
  have hpos : ∀ q, (AlgebraicGeometry.Comparison.Betti.Acyclic.ResolutionCycles.Ext.resolutionSequence K q).Exact := fun q => (I.exact_succ q).map G
  have hK (p q : ℕ) : Subsingleton (Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y)
      (K.X p) (q + 1)) := by
    have : Injective (I.cocomplex.X p) := I.injective p
    have : TopCat.Sheaf.IsFlasque (I.cocomplex.X p) :=
      GeometricComparison.Module.InjectiveFlasque.ModuleInjectiveFlasque.flasque R X.left (I.cocomplex.X p)
    have : TopCat.Sheaf.IsFlasque (K.X p) :=
      GeometricComparison.Module.InjectiveFlasque.ModuleInjectiveFlasque.restriction R (I.cocomplex.X p) f.left
    exact Integral.FlasqueVanishing.IntegralFlasqueVanishing.ext_subsingleton R Y (K.X p) q
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff]
  exact GeometricComparison.Module.AcyclicResolutionSections.ModuleAcyclicResolutionSections.exact_succ R (TopCat.of Y.left) K e w haug hpos hF hK n

theorem forms_ext_subsingleton (j : ℕ) (hj : j ≤ 2) (q : ℕ) :
    Subsingleton (Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y)
      ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f.left).obj
        ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X j)) (q + 1)) := by
  let H := (extFunctor.{1} (q + 1) : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y)ᵒᵖ ⥤
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y ⥤ AddCommGrpCat.{1}).obj (op (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y))
  have : Subsingleton (H.obj ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y).X j)) :=
    FormExtVanishing.IntegralAffineFormExtVanishing.ext_subsingleton R Y j hj q
  let ef : (AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f.left).obj
      ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X j) ≅ (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y).X j :=
    OpenForms.OpenFormsSheaves.sheafIso f j
  let e := H.mapIso ef
  exact (ConcreteCategory.bijective_of_isIso e.hom).injective.subsingleton

theorem forms_exact_succ (j : ℕ) (hj : j ≤ 2)
    (I : InjectiveResolution ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X j)) (n : ℕ) :
    ((((AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f.left) ⋙
      Affine.ChartExtVanishing.AffineChartExtVanishing.sections R Y).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).ExactAt (n + 1) :=
  IntegralAffineRestrictedResolution.exact_succ R f _ I (forms_ext_subsingleton R f j hj) n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.RestrictedResolution.IntegralAffineRestrictedResolution
