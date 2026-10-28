import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ClosedModuleDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.TypePullback
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IdealSheafNilpotence
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # Coherent Closed Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CoherentClosedDescent

noncomputable section

/-! Actual coherent descent to an annihilating closed subscheme, and to
a constructed finite thickening of any closed subset containing the support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem exists_coherent_closed_descent
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (h : f.ker ≤ CoherentAnnihilator.coherentAnnihilator M) :
    ∃ N : X.Modules, N.IsQuasicoherent ∧ N.IsFiniteType ∧
      Nonempty ((pushforward f).obj N ≅ M) := by
  have hi := ClosedModuleDescent.closedModule_unit_isIso_of_ideal_annihilates f M h
  exact ⟨(pullback f).obj M, SheafCohomology.Projective.QuasicoherentAffinePullback.quasicoherent_pullback_of_isAffineHom f M,
    Finite.TypePullback.module_pullback_finiteType f M,
    ⟨(asIso ((pullbackPushforwardAdjunction f).unit.app M)).symm⟩⟩

theorem exists_coherent_on_annihilating_subscheme
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (I : X.IdealSheafData) (h : I ≤ CoherentAnnihilator.coherentAnnihilator M) :
    ∃ N : I.subscheme.Modules, N.IsQuasicoherent ∧ N.IsFiniteType ∧
      Nonempty ((pushforward I.subschemeι).obj N ≅ M) := by
  exact exists_coherent_closed_descent I.subschemeι M (by simpa only [I.ker_subschemeι] using h)

theorem exists_coherent_on_closed_thickening
    {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (I : X.IdealSheafData) (h : (CoherentAnnihilator.coherentAnnihilator M).support ≤ I.support) :
    ∃ (n : ℕ) (N : (I ^ n).subscheme.Modules), N.IsQuasicoherent ∧ N.IsFiniteType ∧
      Nonempty ((pushforward (I ^ n).subschemeι).obj N ≅ M) := by
  obtain ⟨n, hn⟩ := IdealSheafNilpotence.idealSheaf_exists_power_le_of_support_le I (CoherentAnnihilator.coherentAnnihilator M) h
  obtain ⟨N, hq, ht, he⟩ := exists_coherent_on_annihilating_subscheme M (I ^ n) hn
  exact ⟨n, N, hq, ht, he⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CoherentClosedDescent
