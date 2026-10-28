import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.CechSheaf
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange
import OAI.AlgebraicGeometry.SheafCohomology.Cech.FlasqueExact

/-! # Flasque Cech -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Module.FlasqueCech.ModuleFlasqueCech

noncomputable section

/-! Positive-degree Čech cohomology of an actual flasque module sheaf vanishes, by the additive-group comparison of the same cochain complex. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  (F : Sheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R))
  {ι : Type u} (U : ι → X.left.Opens)

def underlyingSheaf : TopCat.Sheaf AddCommGrpCat.{u} X.left :=
  (sheafCompose (Opens.grothendieckTopology X.left) (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F

instance underlyingSheaf_flasque [TopCat.Sheaf.IsFlasque F] :
    TopCat.Sheaf.IsFlasque (underlyingSheaf R X F) where
  epi {V W} i := by
    change Epi ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map (F.obj.map i))
    infer_instance

theorem exactAt_succ [TopCat.Sheaf.IsFlasque F] (hU : iSup U = ⊤) (n : ℕ) :
    ((Cech.CechSheaf.functor R X U).obj F).ExactAt (n + 1) := by
  let G := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let K := (Cech.CechSheaf.functor R X U).obj F
  have h := AlgebraicGeometry.SheafCohomology.Cech.FlasqueExact.TopCat.Sheaf.cechComplex_exactAt_succ_of_isFlasque (underlyingSheaf R X F) U hU n
  have hm : ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).ExactAt (n + 1) :=
    h.of_iso (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk ι U).cech F.obj).symm
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)] at hm ⊢
  exact (ShortComplex.moduleCat_exact_iff _).mpr ((ShortComplex.ab_exact_iff _).mp hm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Module.FlasqueCech.ModuleFlasqueCech
