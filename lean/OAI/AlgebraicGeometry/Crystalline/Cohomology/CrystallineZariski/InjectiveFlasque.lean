import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.GlobalSections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.InjectiveFlasque

/-! # Injective Flasque -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.InjectiveFlasque.CrystallineZariskiInjectiveFlasque

noncomputable section

/-! # The original crystalline injective resolution gives flasque Zariski sheaves -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))
  (F : Sheaf (Site.topology p k X) (ModuleCat.{u + 1} (Site.CoefficientRing p k)))

theorem directImage [Injective F] :
    TopCat.Sheaf.IsFlasque ((Image.CrystallineZariskiImage.functor p k X).obj F) :=
  LargeZariski.InjectiveFlasque.LargeZariskiInjectiveFlasque.flasque (Site.CoefficientRing p k) X.left _

theorem resolution (I : InjectiveResolution F) (q : ℕ) :
    TopCat.Sheaf.IsFlasque ((CechBicomplex.CrystallineZariskiCechBicomplex.imageComplex p k X F I).X q) := by
  have : Injective (I.cocomplex.X q) := I.injective q
  exact directImage p k X (I.cocomplex.X q)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.InjectiveFlasque.CrystallineZariskiInjectiveFlasque
