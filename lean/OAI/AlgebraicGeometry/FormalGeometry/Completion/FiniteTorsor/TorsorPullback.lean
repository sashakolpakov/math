import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullbackIso
import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.GlobalSections
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ShortExactTransport

/-! # Torsor Pullback -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

noncomputable section

/-!
# Completion: inverse image of actual finite-coefficient extensions

Exact inverse image and the proved endpoint comparisons construct the
pulled-back extension. Its extension class is precisely the actual finite
cohomology pullback, so its torsor sections detect vanishing of that class.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite Abelian

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {ℓ n : ℕ} {X Y : Scheme.{u}} (E : App.Construction.FiniteCoefficientExtension ℓ n Y) (f : X ⟶ Y)

/-- The exact inverse image, with its endpoints identified with the actual coefficient sheaves. -/
def App.Construction.FiniteCoefficientExtension.pullbackComplex : ShortComplex (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
  ShortExactTransport.Construction.endpointTransportComplex (E.complex.map (ProetalePullback.Construction.proEtSheafPullback f))
    (asIso (Finite.CoefficientPullback.Construction.proEtFiniteCoefficientPullback ℓ n f))
    ((ProetalePullback.Construction.proEtConstantPullbackIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

theorem App.Construction.FiniteCoefficientExtension.pullbackComplex_shortExact : (E.pullbackComplex f).ShortExact :=
  ShortExactTransport.Construction.endpointTransport_shortExact _ _ _ (E.shortExact.map_of_exact (ProetalePullback.Construction.proEtSheafPullback f))

/-- Pullback of an actual finite-coefficient extension along any scheme morphism. -/
def App.Construction.FiniteCoefficientExtension.pullbackExtension : App.Construction.FiniteCoefficientExtension ℓ n X where
  middle := (E.pullbackComplex f).X₂
  inclusion := (E.pullbackComplex f).f
  projection := (E.pullbackComplex f).g
  zero := (E.pullbackComplex f).zero
  shortExact := E.pullbackComplex_shortExact f

/-- The constructed extension represents the actual pullback of the original H¹ class. -/
theorem App.Construction.FiniteCoefficientExtension.pullbackExtension_extClass :
    (E.pullbackExtension f).extClass = Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n f 1 E.extClass := by
  change (ShortExactTransport.Construction.endpointTransport_shortExact (E.complex.map (ProetalePullback.Construction.proEtSheafPullback f))
    (asIso (Finite.CoefficientPullback.Construction.proEtFiniteCoefficientPullback ℓ n f))
    ((ProetalePullback.Construction.proEtConstantPullbackIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (E.shortExact.map_of_exact (ProetalePullback.Construction.proEtSheafPullback f))).extClass = _
  rw [ShortExactTransport.Construction.endpointTransport_extClass, Finite.CoefficientPullback.Construction.finiteEllAdicPullback_apply]
  erw [App.Construction.FiniteCoefficientExtension.extClass, Ext.mapExactFunctor_extClass]
  rfl

/-- Vanishing after actual pullback is equivalent to a section of the pulled-back extension's torsor. -/
theorem App.Construction.FiniteCoefficientExtension.pullback_eq_zero_iff_fiber_nonempty :
    Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n f 1 E.extClass = 0 ↔
      Nonempty ((E.pullbackExtension f).Fiber (⊤_ X.ProEt)) := by
  rw [← E.pullbackExtension_extClass f]
  exact (E.pullbackExtension f).class_eq_zero_iff_fiber_nonempty

/-- The pulled-back class has a finite étale geometric representative whose section detects zero. -/
theorem App.Construction.FiniteCoefficientExtension.pullback_eq_zero_iff_scheme_section [NeZero (ℓ ^ n)] :
    Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n f 1 E.extClass = 0 ↔
      ∃ s : X ⟶ (E.pullbackExtension f).gluedScheme,
        s ≫ (E.pullbackExtension f).gluedSchemeToBase = 𝟙 X := by
  rw [← E.pullbackExtension_extClass f]
  exact (E.pullbackExtension f).class_eq_zero_iff_scheme_section

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor
