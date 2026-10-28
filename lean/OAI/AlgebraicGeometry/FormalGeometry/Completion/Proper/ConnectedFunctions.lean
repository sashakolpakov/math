import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.Affinization
import OAI.AlgebraicGeometry.FormalGeometry.Completion.NoetherianClosedPoints
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Ideal.GoingUp

/-! # Connected Functions -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ConnectedFunctions.Construction

noncomputable section

/-!
# Completion: global functions of connected reduced proper schemes over a field

The affinization is a connected Noetherian space with closed points, hence
a single point. Reducedness then makes its coordinate ring a field.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K : Type u) [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]

include f

/-- Global functions of a proper scheme over a field have zero-dimensional spectrum. -/
theorem proper_globalFunctions_krullDimLE_zero : Ring.KrullDimLE 0 Γ(X, ⊤) := by
  let F := (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop
  have hF : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  let := F.hom.toAlgebra
  have : Algebra.IsIntegral K Γ(X, ⊤) := algebraMap_isIntegral_iff.mp hF
  exact .mk₀ fun I _ => Ideal.isMaximal_of_isIntegral_of_isMaximal_under
    (R := K) I inferInstance

/-- The spectrum of global functions of a proper scheme over a field is a finite discrete space. -/
theorem proper_globalFunctions_finiteSpectrum : Finite (PrimeSpectrum Γ(X, ⊤)) := by
  have : IsNoetherian X := {
    __ := LocallyOfFiniteType.isLocallyNoetherian f
    __ := QuasiCompact.compactSpace_of_compactSpace f }
  have : NoetherianSpace (PrimeSpectrum Γ(X, ⊤)) :=
    noetherianSpace_of_surjective X.toSpecΓ X.toSpecΓ.continuous
      (Affinization.Construction.proper_toSpecΓ_surjective f).surj
  have := proper_globalFunctions_krullDimLE_zero K f
  have : T1Space (PrimeSpectrum Γ(X, ⊤)) :=
    ⟨fun x => (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mpr inferInstance⟩
  exact NoetherianClosedPoints.Construction.finite_of_noetherian_quasiSober_t1 _

/-- A connected reduced proper scheme over a field has a field of global functions. -/
theorem proper_connected_reduced_globalFunctions_isField
    [ConnectedSpace X] [IsReduced X] : IsField Γ(X, ⊤) := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
  have : Nontrivial Γ(X, ⊤) := inferInstance
  have := proper_globalFunctions_finiteSpectrum K f
  have := proper_globalFunctions_krullDimLE_zero K f
  have : DiscreteTopology (PrimeSpectrum Γ(X, ⊤)) :=
    PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mpr ⟨inferInstance, inferInstance⟩
  have : ConnectedSpace (PrimeSpectrum Γ(X, ⊤)) :=
    (Affinization.Construction.proper_toSpecΓ_surjective f).surj.connectedSpace X.toSpecΓ.continuous
  have : Subsingleton (PrimeSpectrum Γ(X, ⊤)) := subsingleton_of_preconnected_totallyDisconnected
  exact PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mp this

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ConnectedFunctions.Construction
