import OAI.RepresentationTheory.Theta.Adelic.StandardCharacter
import OAI.RepresentationTheory.Theta.Adelic.Construction
import OAI.RepresentationTheory.Theta.Adelic.SiegelBranchFromOscillator
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicOscillatorIdentification

/-! # Oscillator Comparison -/

namespace OAI.RepresentationTheory.Theta.Adelic.OscillatorComparison

noncomputable section

/-! All coordinate, geometric, oscillator, Siegel-branch, lift-uniqueness,
theta-construction, and rational Hecke clauses for the actual comparison
data. Congruence descent is assembled separately. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicOscillatorIdentification.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians OAI.RepresentationTheory.Theta.Adelic.StandardCharacter OAI.RepresentationTheory.Theta.Adelic.Construction
open OAI.RepresentationTheory.Theta.Adelic.HeckeFromOscillator OAI.RepresentationTheory.Theta.Adelic.SiegelBranchFromOscillator OAI.RepresentationTheory.Theta.Adelic.Prerequisites

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)
variable (hd : d ≠ 0) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
variable (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C P)
variable (hS : DataTheta.Descent.StandardArchCharacter (A := A) C.ψ)

include hS

theorem constructedComparison_oscillator :
    DataTheta.OscillatorIdentification (GeometricGaussians.constructedComparison A P) P hd C D :=
  AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicOscillatorIdentification.CM.native_oscillator_identification A P hd C D (StandardCharacter.standardArchCharacter_unique A C hS)

theorem constructedComparison_siegel :
    SiegelBranchData.SiegelBranchExtension (GeometricGaussians.constructedComparison A P) P hd C D :=
  SiegelBranchFromOscillator.constructedComparison_siegel_of_oscillator A P hd C D (constructedComparison_oscillator A P hd C D hS)

theorem constructedComparison_hecke (hds : ¬ IsSquare d)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val) :
    DataTheta.Descent.RationalHeckeCovariance (GeometricGaussians.constructedComparison A P) P hd C D :=
  HeckeFromOscillator.constructedComparison_hecke_of_oscillator A P hd C D hds hH hK
    (constructedComparison_oscillator A P hd C D hS)

theorem constructedComparison_full_analytic (h : Prerequisites.ThetaInput.{0}) (hds : ¬ IsSquare d)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val) :
    DataTheta.CoordinateIdentification (GeometricGaussians.constructedComparison A P) P ∧
    DataTheta.GeometryIdentification (GeometricGaussians.constructedComparison A P) ∧
    DataTheta.OscillatorIdentification (GeometricGaussians.constructedComparison A P) P hd C D ∧
    SiegelBranchData.SiegelBranchExtension (GeometricGaussians.constructedComparison A P) P hd C D ∧
    SiegelBranchData.ArchimedeanLiftUniqueness P hd C D ∧
    DataTheta.Descent.ThetaConstruction (GeometricGaussians.constructedComparison A P) ∧
    DataTheta.Descent.RationalHeckeCovariance (GeometricGaussians.constructedComparison A P) P hd C D :=
  ⟨GeometricGaussians.constructedComparison_coordinates A P, GeometricGaussians.constructedComparison_geometry A P,
    constructedComparison_oscillator A P hd C D hS, constructedComparison_siegel A P hd C D hS,
    AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicArchimedeanLift.CM.native_archimedean_lift_uniqueness A P hd C D, Construction.constructedComparison_theta A P h,
    constructedComparison_hecke A P hd C D hS hds hH hK⟩

end

end OAI.RepresentationTheory.Theta.Adelic.OscillatorComparison
