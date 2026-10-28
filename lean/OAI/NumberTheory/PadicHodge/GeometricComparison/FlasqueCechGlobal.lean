import OAI.NumberTheory.PadicHodge.GeometricComparison.ModuleCechTopRestriction
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TopRestrictionNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalEdge
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits

/-! # Flasque Cech Global -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechGlobal.FlasqueCechGlobalComparison

noncomputable section

/-! A complex of flasque module sheaves computes its original Cech total
from its actual global sections, through canonical restriction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u v w
variable (R : Type u) [CommRing R] (X : TopCat.{v})
  {ι : Type} (U : ι → Opens X)
  (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v w} R)) ℕ)

local instance cech_additive : (cechComplexFunctor (A := ModuleCat.{max u v w} R) U).Additive := by
  change (FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk ι U).cech).Additive
  infer_instance

def presheafComplex : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{max u v w} R) ℕ :=
  ((sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v w} R)).mapHomologicalComplex (.up ℕ)).obj K

def globalComplex : CochainComplex (ModuleCat.{max u v w} R) ℕ :=
  (((evaluation (Opens X)ᵒᵖ (ModuleCat.{max u v w} R)).obj (op ⊤)).mapHomologicalComplex (.up ℕ)).obj
    (presheafComplex R X K)

def bicomplex : HomologicalComplex₂ (ModuleCat.{max u v w} R) (.up ℕ) (.up ℕ) :=
  ((cechComplexFunctor U).mapHomologicalComplex (.up ℕ)).obj (presheafComplex R X K)

def component (q : ℕ) : (globalComplex R X K).X q ⟶ ((FlasqueCechGlobalComparison.bicomplex R X U K).X q).X 0 :=
  Cech.TopRestriction.CechTopRestriction.map (Opens X) U (K.X q).obj

theorem comm (q q' : ℕ) : component R X U K q ≫ ((FlasqueCechGlobalComparison.bicomplex R X U K).d q q').f 0 =
    (globalComplex R X K).d q q' ≫ component R X U K q' :=
  Cech.TopRestrictionNaturality.CechTopRestrictionNaturality.map (Opens X) U ((K.d q q').hom)

theorem cocycle (q : ℕ) : component R X U K q ≫ ((FlasqueCechGlobalComparison.bicomplex R X U K).X q).d 0 1 = 0 :=
  Cech.TopRestriction.CechTopRestriction.map_comp_d (Opens X) U (K.X q).obj

local instance hasTotal : (FlasqueCechGlobalComparison.bicomplex R X U K).HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts _

def map : globalComplex R X K ⟶ (FlasqueCechGlobalComparison.bicomplex R X U K).total (.up ℕ) :=
  (AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge (bicomplex R X U K)) (globalComplex R X K) (component R X U K)
    (fun q q' _ => comm R X U K q q') (cocycle R X U K)

theorem quasiIso (hU : iSup U = ⊤)
    (hK : ∀ q, TopCat.Presheaf.IsFlasque (X := X) (K.X q).obj) :
    QuasiIso (map R X U K) := by
  apply Module.TotalEdge.ModuleTotalEdge.quasiIso.{u, max v w} R (FlasqueCechGlobalComparison.bicomplex R X U K) (globalComplex R X K)
    (component R X U K) (fun q q' _ => comm R X U K q q') (cocycle R X U K)
  · intro q
    exact (ModuleCechTopRestriction.LargeModuleCechTopRestriction.exact_and_mono R X (K.X q) U hU).1
  · intro q
    exact (ModuleCechTopRestriction.LargeModuleCechTopRestriction.exact_and_mono R X (K.X q) U hU).2
  · intro q r
    let := hK q
    exact LargeModuleAt.LargeModuleFlasqueCech.exactAt_succ R X (K.X q) U hU r

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechGlobal.FlasqueCechGlobalComparison
