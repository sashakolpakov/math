import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.UnitarySymplectic
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.HeisenbergCovariance
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.HeisenbergFamily

/-! # Unitary Heisenberg -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.UnitaryHeisenberg.CM

noncomputable section

/-! The actual normalized unitary splittings satisfy local Heisenberg
covariance for the assembled finite-adelic symplectic action. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.UnitarySymplectic.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.FiniteSymplectic.CM

variable (F : Type) [Field F] [NumberField F] (d : F) (n m : ℕ)
  (H : (Matrix (Fin n) (Fin n) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
  (K : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
  (hd : d ≠ 0) (C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d n m) (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d n m H K)
  (D : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)

local instance (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
local instance (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) : CharZero (v.adicCompletion F) := RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionCharZero F (.inr v)

theorem assembled_phase_local (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H)
    (z : (Fin (n * m) ⊕ Fin (n * m)) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) :
    (fun i => ((UnitarySymplectic.CM.assembled F d n m H K hd C P D g).val *ᵥ z) i v) =
      RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (UnitarySymplectic.CM.localHom F d n m H K P v (g v)) (fun i => z i v) := by
  have hm := congrArg Subtype.val (UnitarySymplectic.CM.assembled_local F d n m H K hd C P D g v)
  change (UnitarySymplectic.CM.assembled F d n m H K hd C P D g).val.map (HeckeCycles.NumberField.FiniteSymplectic.CM.evaluation F v) =
    (UnitarySymplectic.CM.localHom F d n m H K P v (g v)).val at hm
  funext i
  exact (RingHom.map_mulVec (HeckeCycles.NumberField.FiniteSymplectic.CM.evaluation F v) (UnitarySymplectic.CM.assembled F d n m H K hd C P D g).val z i).trans
    (congrFun (congrArg (fun A => A *ᵥ (fun j => z j v)) hm) i)

theorem local_covariance (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H)
    (z : (Fin (n * m) ⊕ Fin (n * m)) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F)
    (f : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) (n * m)) :
    RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUAction F H K hd C P D v (g v)
      (HeckeCycles.NumberField.HeisenbergFamily.CM.Family.localOperator F (n * m) C.ψ C.ψ_unitary C.ψ_continuous z v f) =
      HeckeCycles.NumberField.HeisenbergFamily.CM.Family.localOperator F (n * m) C.ψ C.ψ_unitary C.ψ_continuous
        ((UnitarySymplectic.CM.assembled F d n m H K hd C P D g).val *ᵥ z) v
        (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUAction F H K hd C P D v (g v) f) := by
  have hp : RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localProjection (v.adicCompletion F) (n * m) (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
      (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUSplitting F H K hd C P D (.inr v) (g v)) = UnitarySymplectic.CM.localHom F d n m H K P v (g v) :=
    D.covers (.inr v) (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUToPair F H K (.inr v) (g v))
  have ht := Local.HeisenbergCovariance.CM.covariance
    (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
    (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_unitary F C.ψ C.ψ_unitary (.inr v))
    (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_continuous F C.ψ C.ψ_continuous (.inr v))
    (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUSplitting F H K hd C P D (.inr v) (g v)) (fun i => z i v) f
  rw [hp] at ht
  exact ht.trans (congrArg
    (fun u => IntegralHeisenberg.CM.operator (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
      (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_unitary F C.ψ C.ψ_unitary (.inr v))
      (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_continuous F C.ψ C.ψ_continuous (.inr v)) u
      (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUAction F H K hd C P D v (g v) f))
    (assembled_phase_local F d n m H K hd C P D g z v).symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.UnitaryHeisenberg.CM
