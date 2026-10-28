import OAI.RepresentationTheory.Theta.Adelic.IntrinsicRegularity
import OAI.RepresentationTheory.Theta.Adelic.ConstructNormalizedSplittings
import OAI.RepresentationTheory.Theta.Adelic.Characters
import OAI.RepresentationTheory.Theta.Adelic.CongruenceLevel
import OAI.RepresentationTheory.Theta.Adelic.SplitCoordinates
import OAI.RepresentationTheory.Theta.Adelic.OscillatorComparison
import OAI.RepresentationTheory.Theta.Adelic.CongruenceDescent
import OAI.RepresentationTheory.Weil.AdelicSplitting.No
import OAI.GroupTheory.LinearGroups.SpecialLinearPerfect

/-! # Unitary Theta Congruence -/

namespace OAI.RepresentationTheory.Theta.Adelic.UnitaryThetaCongruence

noncomputable section

/-! The complete repaired AdelicTheta with no result-level prerequisites.

Characters and exactly normalized local splittings are constructed from the
arithmetic data. Proved AdelicSplitting supplies their rational compatibility. Completed
theta regularity uses only the direct lattice analysis, and Gaussian/frame
comparison gives the actual oscillator and geometric transformations.
Principal congruence descent uses the concrete arithmetic construction.
The historical conditional entrypoints and counterexamples are preserved.
-/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.Data OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.CongruenceLevel
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians
open OAI.RepresentationTheory.Theta.Adelic.OscillatorComparison OAI.RepresentationTheory.Theta.Adelic.CongruenceDescent

/-- Arbitrary nondegenerate Hermitian/skew-Hermitian spaces: the characters,
normalized local lifts, adelic factorization and rational compatibility are
all conclusions. A global frame specifies only linear symplectic coordinates. -/
theorem general_splitting : Data.GeneralSplittingStatement := by
  intro F _ _ d hq n m hnm H K hH hK ψ hc hu hn hp P
  obtain ⟨C, hC, hchar⟩ := Characters.complete_character_conclusion
    F d hq.1 hq.2 n m ψ hc hu hn hp
  obtain ⟨D⟩ := ConstructNormalizedSplittings.exists_normalized_local_splittings
    F d hq.1 hq.2 n m hnm H K hH hK C P
  refine ⟨C, hC, hchar, D, ?_, ?_⟩
  · exact Weil.AdelicSplitting.No.adelic_unitary_splitting_compatible_with_rational_points
      F d hq n m H K hH hK C P D
  · exact ⟨FiniteSchwartz.finiteAction_smooth F H K hq.1 C P D hnm,
      CongruenceLevel.finite_family_congruence_level F d hq.1 n m hnm H K C P D⟩

local instance (F : Type) [Field F] [NumberField F] (v : FiniteSchwartz.FinitePlace F) :
    MeasurableSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) := borel _
local instance (F : Type) [Field F] [NumberField F] (v : FiniteSchwartz.FinitePlace F) :
    BorelSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) := ⟨rfl⟩

/-- The split polarization and literal substitution are constructed;
elementary SL₃ perfectness removes character ambiguity. -/
theorem split_substitution : Data.SplitMultiplicityOneStatement := by
  intro F _ _ d hd H K hH hK C P D v r hr
  constructor
  · exact SplitCoordinates.split_polarization_substitution F d H K P v hd C D
      (ConstructSplitPolarization.constructedSplitPolarization F d hd H K hH hK P v r hr)
  · intro χ g
    exact congrArg (fun f : Matrix.SpecialLinearGroup (Fin 3) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) →* Circle => f g)
      (GroupTheory.LinearGroups.SpecialLinearPerfect.SLConstruction.sl3_hom_to_abelian_eq_one (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) Circle χ)

/-- Full geometric, Gaussian, Siegel-branch, completed-theta and genuine
principal-congruence conclusions for the same constructed local/global lift. -/
theorem ball_theta_and_congruence : Data.BallCompletedThetaStatement := by
  intro F _ _ d hq m hm H K hH hK ψ hc hu hn hp P A hS
  have hnm : 0 < 3 * m := by rcases hm with rfl | rfl <;> norm_num
  obtain ⟨C, hC, hchar, D, hAdelic, hfinite⟩ := general_splitting
    F d hq 3 m hnm H K hH hK ψ hc hu hn hp P
  have hSC : DataTheta.Descent.StandardArchCharacter (A := A) C.ψ := hC.symm ▸ hS
  have htheta := IntrinsicRegularity.IntrinsicTheta.constructedComparison_theta A P
  have hhecke := OscillatorComparison.constructedComparison_hecke A P hq.1 C D hSC hq.2 hH hK
  refine ⟨C, hC, hchar, D, hAdelic, hfinite, GeometricGaussians.constructedComparison A P,
    GeometricGaussians.constructedComparison_coordinates A P, GeometricGaussians.constructedComparison_geometry A P,
    OscillatorComparison.constructedComparison_oscillator A P hq.1 C D hSC,
    OscillatorComparison.constructedComparison_siegel A P hq.1 C D hSC, ?_, htheta, hhecke, ?_⟩
  · exact AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicArchimedeanLift.CM.native_archimedean_lift_uniqueness A P hq.1 C D
  · exact CongruenceDescent.constructedComparison_congruence A P hq.1 C D hH hfinite htheta hhecke

/-- Exactly the preserved full repaired statement; no prerequisite bundle,
Poisson identity, oscillator comparison or congruence result is assumed. -/
theorem complete_unitary_splitting_geometric_theta_and_congruence : Data.CompleteStatement :=
  ⟨general_splitting, split_substitution, ball_theta_and_congruence⟩

end

end OAI.RepresentationTheory.Theta.Adelic.UnitaryThetaCongruence
