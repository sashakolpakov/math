import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Contraction

/-! # Coefficients -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Coefficients.MixedCechCoefficients

noncomputable section

/-! # Open restriction with independent scheme and coefficient universes -/

open _root_.CategoryTheory Opposite _root_.AlgebraicGeometry

universe u v

variable (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens) (i : ι)
  (R : Type v) [CommRing R]

def restricted (P : X.Opensᵒᵖ ⥤ ModuleCat.{max u v} R) :
    (U i).toScheme.Opensᵒᵖ ⥤ ModuleCat.{max u v} R :=
  (U i).ι.opensFunctor.op ⋙ P

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Coefficients.MixedCechCoefficients
