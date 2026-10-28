import OAI.RepresentationTheory.Theta.Adelic.GeometricTensorSmoothness
import OAI.RepresentationTheory.Theta.Adelic.GaussianProduct

/-! # Construction -/

namespace OAI.RepresentationTheory.Theta.Adelic.Construction

noncomputable section

/-! All clauses of the actual theta-construction predicate, including
its discrete lattice model and smooth geometric Taylor tensors. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians OAI.RepresentationTheory.Theta.Adelic.LatticeIdentification OAI.RepresentationTheory.Theta.Adelic.Regularity
open OAI.RepresentationTheory.Theta.Adelic.GaussianProduct.ThetaComparison OAI.RepresentationTheory.Theta.Adelic.GeometricTensorSmoothness OAI.RepresentationTheory.Theta.Adelic.Prerequisites

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem constructedComparison_theta (h : Prerequisites.ThetaInput.{0}) :
    DataTheta.Descent.ThetaConstruction (GeometricGaussians.constructedComparison A P) :=
  ⟨LatticeIdentification.constructedComparison_lattice A P, LatticeIdentification.rationalTheta_summable A P,
    GaussianProduct.ThetaComparison.rationalTheta_native A P, Regularity.completedTensor_smooth A P h,
    Regularity.completedTensor_symmetric A P h, GeometricTensorSmoothness.geometricTensor_smooth A P h⟩

end

end OAI.RepresentationTheory.Theta.Adelic.Construction
