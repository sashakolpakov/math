import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.PicardPeriodQuotient
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.Add

/-! # Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.Scalars

noncomputable section

/-! The actual native holomorphic H1 group carries its canonical complex
scalar action induced by multiplication on the coefficient sheaf. -/

open _root_.CategoryTheory _root_.TopologicalSpace

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (M : Type) [TopologicalSpace M] [ChartedSpace E M]

local instance nativeHolomorphicH1Group :
    AddCommGroup (CategoryTheory.Sheaf.H (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 1) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of M) (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 1

@[instance_reducible]
def nativeHolomorphicH1Module : Module ℂ (CategoryTheory.Sheaf.H (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 1) where
  smul c x := RepresentationTheory.Theta.Geometric.Holomorphic.PicardPeriodQuotient.holomorphicScalarH1 E M c x
  one_smul := RepresentationTheory.Theta.Geometric.Holomorphic.PicardPeriodQuotient.holomorphicScalarH1_one E M
  mul_smul c d x := (RepresentationTheory.Theta.Geometric.Holomorphic.PicardPeriodQuotient.holomorphicScalarH1_mul E M c d x).symm
  smul_zero c := (RepresentationTheory.Theta.Geometric.Holomorphic.PicardPeriodQuotient.holomorphicScalarH1 E M c).map_zero
  smul_add c x y := (RepresentationTheory.Theta.Geometric.Holomorphic.PicardPeriodQuotient.holomorphicScalarH1 E M c).map_add x y
  add_smul := RepresentationTheory.Theta.Geometric.Holomorphic.PicardPeriodQuotient.holomorphicScalarH1_add E M
  zero_smul x := by
    change RepresentationTheory.Theta.Geometric.Holomorphic.PicardPeriodQuotient.holomorphicScalarH1 E M 0 x = 0
    simpa only [Nat.cast_zero] using (RepresentationTheory.Theta.Geometric.Holomorphic.PicardPeriodQuotient.holomorphicScalarH1_natCast E M 0 x).trans (zero_nsmul x)

theorem nativeHolomorphicH1Module_smul (c : ℂ)
    (x : CategoryTheory.Sheaf.H (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 1) :
    letI := nativeHolomorphicH1Module E M
    c • x = CategoryTheory.Sheaf.H.map (RepresentationTheory.Theta.Geometric.Holomorphic.PicardPeriodQuotient.holomorphicScalarSheafMap E M c) 1 x := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.Scalars
