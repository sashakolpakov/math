import OAI.RepresentationTheory.Theta.Adelic.HeckeFromOscillator
import OAI.RepresentationTheory.Theta.Adelic.SiegelBranchCocycle
import OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData

/-! # Siegel Branch From Oscillator -/

namespace OAI.RepresentationTheory.Theta.Adelic.SiegelBranchFromOscillator

noncomputable section

/-! The full geometric Siegel branch becomes the unique extension of
the actual Gaussian-operator branch after their line actions agree. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians
open OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData OAI.RepresentationTheory.Theta.Adelic.GeometricSiegelBranch OAI.RepresentationTheory.Theta.Adelic.SiegelBranchCocycle OAI.RepresentationTheory.Theta.Adelic.HeckeFromOscillator

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)
variable (hd : d ≠ 0) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
variable (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C P)

theorem constructedComparison_siegel_of_oscillator
    (hO : DataTheta.OscillatorIdentification (GeometricGaussians.constructedComparison A P) P hd C D) :
    SiegelBranchData.SiegelBranchExtension (GeometricGaussians.constructedComparison A P) P hd C D := by
  refine ⟨GeometricSiegelBranch.geometricSiegelBranch A P, GeometricSiegelBranch.geometricSiegelBranch_holomorphic A P,
    GeometricSiegelBranch.geometricSiegelBranch_continuous A P, GeometricSiegelBranch.geometricSiegelBranch_square A P, ?_,
    SiegelBranchCocycle.geometricSiegelBranch_mul A P, SiegelBranchCocycle.geometricSiegelBranch_one A P, ?_⟩
  · intro g z
    exact (GeometricSiegelBranch.geometricSiegelBranch_ball A P g z).trans
      (HeckeFromOscillator.oscillatorFactor_eq_geometric_of_line A P hd C D hO g z).symm
  · intro g j hj hs hb Z
    apply GeometricSiegelBranch.geometricSiegelBranch_unique A P g j hj hs
    obtain ⟨z, hz⟩ := hb
    exact ⟨z, hz.trans (HeckeFromOscillator.oscillatorFactor_eq_geometric_of_line A P hd C D hO g z)⟩

end

end OAI.RepresentationTheory.Theta.Adelic.SiegelBranchFromOscillator
