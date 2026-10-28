import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ArchimedeanUnitaryPerfect
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PerfectOscillatorUniqueness
import OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData
import OAI.RepresentationTheory.Theta.Adelic.FiniteCharacterNontrivial

/-! # Intrinsic Archimedean Lift -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicArchimedeanLift.CM

noncomputable section

/-! The actual normalized native splittings at all real places lie in
the bare metaplectic groups and satisfy the full lift-uniqueness clause. -/

open scoped _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData

local instance nativeArchLiftMeasurable (F : Type) [Field F] [NumberField F] (v : NumberField.InfinitePlace F) :
    MeasurableSpace (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := borel _
local instance nativeArchLiftBorel (F : Type) [Field F] [NumberField F] (v : NumberField.InfinitePlace F) :
    BorelSpace (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := ⟨rfl⟩

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W)
  (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H W) (hd : d ≠ 0) (C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
  (D : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H W hd C P)

include A in
theorem native_real_splitting_metaplectic (v : NumberField.InfinitePlace F)
    (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl v))) :
    RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUSplitting F H W hd C P D (.inl v) g ∈
      RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticSubgroup (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) (3 * m) (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inl v)) :=
  BallPerfect.CM.perfect_oscillator_lift_mem_metaplectic (ArchimedeanUnitaryPerfect.CM.native_real_unitary_perfect A v)
    (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inl v))
    (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUSplitting F H W hd C P D (.inl v)).toMonoidHom g

include A in
theorem native_archimedean_lift_uniqueness : RepresentationTheory.Theta.Adelic.SiegelBranchData.ArchimedeanLiftUniqueness P hd C D := by
  intro v s hs
  have : CharZero (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionCharZero F (.inl v)
  have hc := RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_continuous F C.ψ C.ψ_continuous (.inl v)
  have hu := RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_unitary F C.ψ C.ψ_unitary (.inl v)
  have hn := RepresentationTheory.Theta.Adelic.FiniteCharacterNontrivial.local_character_nontrivial F C.ψ
    C.ψ_continuous C.ψ_unitary C.ψ_nontrivial C.ψ_principal (.inl v)
  have he := PerfectOscillatorUniqueness.CM.perfect_oscillator_lifts_agree (ArchimedeanUnitaryPerfect.CM.native_real_unitary_perfect A v)
    (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inl v)) hc hu (RepresentationTheory.Weil.AdelicSplitting.LocalKernel.Construction.completion_nondiscrete F (.inl v)) hn
    s.toMonoidHom (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUSplitting F H W hd C P D (.inl v)).toMonoidHom
    (fun g => (hs g).trans (D.covers (.inl v) (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUToPair F H W (.inl v) g)).symm)
  intro g
  exact DFunLike.congr_fun he g

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicArchimedeanLift.CM
