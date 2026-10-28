import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechComplex

/-! # Intrinsic De Rham Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Small.IntrinsicDeRhamTotal.Intrinsic

noncomputable section

/-! The small-cover de Rham complex is the literal native sheafified
Čech total over the same opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  [IsProper X.hom] [Smooth X.hom]

def iso : AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total R X ≅
    IntrinsicDeRham.CechComplex.Intrinsic.total R X (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens R X) := Iso.refl _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Small.IntrinsicDeRhamTotal.Intrinsic
