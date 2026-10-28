import OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechGlobal

/-! # Flasque Cech Total -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechTotal.FlasqueCechGlobalNaturality

noncomputable section

/-! Canonical global-section restriction to the Cech total is natural in complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

open OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechGlobal.FlasqueCechGlobalComparison
universe u v w
variable (R : Type u) [CommRing R] (X : TopCat.{v}) {ι : Type} (U : ι → Opens X)
  {K L : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v w} R)) ℕ}
  (a : K ⟶ L)

local instance cech_additive : (cechComplexFunctor (A := ModuleCat.{max u v w} R) U).Additive := by
  change (FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk ι U).cech).Additive
  infer_instance

def presheafMap :=
  ((sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v w} R)).mapHomologicalComplex (.up ℕ)).map a

def globalMap : FlasqueCechGlobal.FlasqueCechGlobalComparison.globalComplex R X K ⟶ FlasqueCechGlobal.FlasqueCechGlobalComparison.globalComplex R X L :=
  (((evaluation (Opens X)ᵒᵖ (ModuleCat.{max u v w} R)).obj (op ⊤)).mapHomologicalComplex (.up ℕ)).map
    (presheafMap R X a)

def bicomplexMap : FlasqueCechGlobal.FlasqueCechGlobalComparison.bicomplex R X U K ⟶ FlasqueCechGlobal.FlasqueCechGlobalComparison.bicomplex R X U L :=
  ((cechComplexFunctor U).mapHomologicalComplex (.up ℕ)).map (presheafMap R X a)

def totalMap : (FlasqueCechGlobal.FlasqueCechGlobalComparison.bicomplex R X U K).total (.up ℕ) ⟶ (FlasqueCechGlobal.FlasqueCechGlobalComparison.bicomplex R X U L).total (.up ℕ) :=
  HomologicalComplex₂.total.map (bicomplexMap R X U a) (.up ℕ)

theorem natural : FlasqueCechGlobal.FlasqueCechGlobalComparison.map R X U K ≫ totalMap R X U a = globalMap R X a ≫ FlasqueCechGlobal.FlasqueCechGlobalComparison.map R X U L := by
  apply HomologicalComplex.Hom.ext
  funext q
  have h : FlasqueCechGlobal.FlasqueCechGlobalComparison.component R X U K q ≫ ((bicomplexMap R X U a).f q).f 0 =
      (globalMap R X a).f q ≫ FlasqueCechGlobal.FlasqueCechGlobalComparison.component R X U L q :=
    Cech.TopRestrictionNaturality.CechTopRestrictionNaturality.map (Opens X) U (a.f q).hom
  change (FlasqueCechGlobal.FlasqueCechGlobalComparison.component R X U K q ≫ (FlasqueCechGlobal.FlasqueCechGlobalComparison.bicomplex R X U K).ιTotal (.up ℕ) q 0 q rfl) ≫
      (HomologicalComplex₂.total.map (bicomplexMap R X U a) (.up ℕ)).f q =
    (globalMap R X a).f q ≫ FlasqueCechGlobal.FlasqueCechGlobalComparison.component R X U L q ≫ (FlasqueCechGlobal.FlasqueCechGlobalComparison.bicomplex R X U L).ιTotal (.up ℕ) q 0 q rfl
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc, h, Category.assoc]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechTotal.FlasqueCechGlobalNaturality
