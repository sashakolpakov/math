import OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalKernelConeHomology
import OAI.AlgebraicTopology.Singular.SheafCochainOpenCone

/-! # Canonical Relative Cone Coefficients -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalRelativeConeCoefficients

noncomputable section

/-! # The original canonical relative-cone equivalence preserves rational coefficients -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Singular

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The two actual kernel/cone normalizations cancel after applying the coefficient functor. -/
theorem shortExactHomologyIsoCone_map_cancel (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (n n' : ℤ) (h : 1 + n = n') :
    (Algebra.Homology.CoconeShortExactNaturality.CochainComplex.mappingCocone.shortExactHomologyIsoCone
      (S.map (F.mapHomologicalComplex (.up ℤ)))
      (hS.map_of_exact (F.mapHomologicalComplex (.up ℤ))) n n' h).hom ≫
      HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.mapHomologicalComplexIso S.g F).inv n ≫
      (((CochainComplex.mappingCone S.g).sc n).mapHomologyIso F).hom ≫
      F.map (Algebra.Homology.CoconeShortExactNaturality.CochainComplex.mappingCocone.shortExactHomologyIsoCone S hS n n' h).inv =
    ((S.X₁.sc n').mapHomologyIso F).hom := by
  have hc := congrArg (fun f => f ≫
    F.map (Algebra.Homology.CoconeShortExactNaturality.CochainComplex.mappingCocone.shortExactHomologyIsoCone S hS n n' h).inv)
    (CanonicalKernelConeHomology.shortExactHomologyIsoCone_map S hS F n n' h).symm
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id] at hc
  change _ = ((S.X₁.sc n').mapHomologyIso F).hom ≫
    F.map (𝟙 (S.X₁.sc n').homology) at hc
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at hc
  exact hc

variable (Y : TopCat.{0}) (U V : Opens Y)

local notation "F" => forget₂ (ModuleCat ℚ) AddCommGrpCat
local notation "FI" => Functor.mapHomologicalComplex (F) (ComplexShape.up ℤ)
local notation "P" => OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openInclusionPair Y (Opens.infLELeft V U)
local notation "S" => OAI.AlgebraicTopology.Singular.RelativeCochainCone.relativeDualCochainShortComplexInt ℚ (P)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Returning from the actual raw cone recovers the original relative cohomology class. -/
theorem originalOpenRelativeCone_normalization (n : ℕ)
    (a : ((FI).obj (S).X₁).homology (n : ℤ)) :
    AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionConeCohomologyEquivRelative ℚ Y (Opens.infLELeft V U) n
      ((HomologicalComplex.homologyMap
        (AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionConeIsoRelative ℚ Y (Opens.infLELeft V U)).inv
        ((n : ℤ) - 1))
        ((Algebra.Homology.CoconeShortExactNaturality.CochainComplex.mappingCocone.shortExactHomologyIsoCone ((S).map (FI))
          ((AlgebraicTopology.Singular.RelativeCochainG.relativeDualCochainShortComplexInt_shortExact ℚ (P)).map_of_exact (FI))
          ((n : ℤ) - 1) n (by omega)).hom a)) =
    AlgebraicTopology.Singular.RelativeCochainConeNaturality.relativeDualCochainCohomologyEquiv ℚ (P) n
      ((((S).X₁.sc (n : ℤ)).mapHomologyIso (F)).hom a) := by
  let er := HomologicalComplex.homologyMapIso
    (AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionConeIsoRelative ℚ Y (Opens.infLELeft V U)) ((n : ℤ) - 1)
  let ec := HomologicalComplex.homologyMapIso
    (CochainComplex.mappingCone.mapHomologicalComplexIso (S).g (F)) ((n : ℤ) - 1)
  let eh := ((CochainComplex.mappingCone (S).g).sc ((n : ℤ) - 1)).mapHomologyIso (F)
  let es := AlgebraicTopology.Singular.RelativeCochainConeNaturality.relativeDualCochainHomologyIsoCone ℚ (P) n
  let em := Algebra.Homology.CoconeShortExactNaturality.CochainComplex.mappingCocone.shortExactHomologyIsoCone ((S).map (FI))
    ((AlgebraicTopology.Singular.RelativeCochainG.relativeDualCochainShortComplexInt_shortExact ℚ (P)).map_of_exact (FI))
    ((n : ℤ) - 1) n (by omega)
  change (AlgebraicTopology.Singular.RelativeCochainConeNaturality.relativeDualCochainCohomologyEquiv ℚ (P) n)
    (((F).map es.inv) (eh.hom (ec.inv (er.hom (er.inv (em.hom a)))))) = _
  rw [Iso.inv_hom_id_apply]
  change (AlgebraicTopology.Singular.RelativeCochainConeNaturality.relativeDualCochainCohomologyEquiv ℚ (P) n)
    ((em.hom ≫ ec.inv ≫ eh.hom ≫ (F).map es.inv) a) = _
  exact congrArg (fun f => AlgebraicTopology.Singular.RelativeCochainConeNaturality.relativeDualCochainCohomologyEquiv ℚ (P) n (f a))
    (shortExactHomologyIsoCone_map_cancel (S)
      (AlgebraicTopology.Singular.RelativeCochainG.relativeDualCochainShortComplexInt_shortExact ℚ (P)) (F)
      ((n : ℤ) - 1) n (by omega))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalRelativeConeCoefficients
