import OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCover
import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-! # Large Module At -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LargeModuleAt.LargeModuleFlasqueCech

noncomputable section

/-! The original small-cover Cech complex of a large flasque module sheaf
is exact in positive degrees. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u v w
variable (R : Type u) [CommRing R] (X : TopCat.{v})
  (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v w} R))
  {ι : Type} (U : ι → Opens X)

def underlyingSheaf : TopCat.Sheaf AddCommGrpCat.{max u v w} X :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat.{max u v w} R) AddCommGrpCat.{max u v w})).obj F

instance underlying_flasque [hF : TopCat.Presheaf.IsFlasque (X := X) F.obj] :
    TopCat.Sheaf.IsFlasque (underlyingSheaf R X F) where
  epi i := by
    let := hF.epi i
    change Epi ((forget₂ (ModuleCat.{max u v w} R) AddCommGrpCat.{max u v w}).map (F.obj.map i))
    infer_instance

theorem exactAt_succ [TopCat.Presheaf.IsFlasque (X := X) F.obj] (hU : iSup U = ⊤) (n : ℕ) :
    ((cechComplexFunctor U).obj F.obj).ExactAt (n + 1) := by
  let G := forget₂ (ModuleCat.{max u v w} R) AddCommGrpCat.{max u v w}
  let K := (cechComplexFunctor U).obj F.obj
  have h := SmallCover.SmallCoverFlasqueCech.exactAt_succ.{v, max u w} X (underlyingSheaf R X F) U hU n
  have hm : ((G.mapHomologicalComplex (.up ℕ)).obj K).ExactAt (n + 1) :=
    h.of_iso (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk ι U).cech F.obj).symm
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)] at hm ⊢
  exact (ShortComplex.moduleCat_exact_iff _).mpr ((ShortComplex.ab_exact_iff _).mp hm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LargeModuleAt.LargeModuleFlasqueCech
