import OAI.NumberTheory.PadicHodge.IntegralComparison.EtalePullbackGlobalSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.CoverCharacter
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ShortExactTransport

/-! # Presentation Pullback -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PresentationPullback

noncomputable section

/-! The actual inverse image of a finite-coefficient presentation has
the original finite-cohomology pullback as its connecting homomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Abelian

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.AlgebraicGeometry.FormalGeometry.Completion.ShortExactTransport.Construction OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CoverCocycles OAI.NumberTheory.PadicHodge.IntegralComparison.EtalePullbackGlobalSections.Pro

universe u
variable (ℓ n : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)
  (I Q : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
  (i : AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n Y ⟶ I) (g : I ⟶ Q) (h : i ≫ g = 0)

abbrev source := ShortComplex.mk i g h

def complex : ShortComplex (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
  AlgebraicGeometry.FormalGeometry.Completion.ShortExactTransport.Construction.endpointTransportComplex ((source ℓ n I Q i g h).map (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f))
    (asIso (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientPullback ℓ n f)) (Iso.refl _)

omit [Fact (Nat.Prime ℓ)] in
theorem shortExact (hS : (source ℓ n I Q i g h).ShortExact) :
    (complex ℓ n f I Q i g h).ShortExact :=
  AlgebraicGeometry.FormalGeometry.Completion.ShortExactTransport.Construction.endpointTransport_shortExact _ _ _ (hS.map_of_exact (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f))

omit [Fact (Nat.Prime ℓ)] in
theorem coefficient_comp_f : AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientPullback ℓ n f ≫
    (complex ℓ n f I Q i g h).f = (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f).map i := by
  change AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientPullback ℓ n f ≫
    (inv (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientPullback ℓ n f) ≫ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f).map i) = _
  rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

omit [Fact (Nat.Prime ℓ)] in
theorem connecting (hS : (source ℓ n I Q i g h).ShortExact)
    (z : Q.obj.obj (op (⊤_ Y.ProEt))) :
    CoverCocycles.connectingSections (complex ℓ n f I Q i g h) (shortExact ℓ n f I Q i g h hS)
      (EtalePullbackGlobalSections.Pro.globalMap f Q z) =
        AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n f 1 (CoverCocycles.connectingSections (source ℓ n I Q i g h) hS z) := by
  change ((Sheaf.H.equiv₀ ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f).obj Q) terminalIsTerminal).symm
    (EtalePullbackGlobalSections.Pro.globalMap f Q z)).comp
      (AlgebraicGeometry.FormalGeometry.Completion.ShortExactTransport.Construction.endpointTransport_shortExact ((source ℓ n I Q i g h).map (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f))
        (asIso (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientPullback ℓ n f)) (Iso.refl _)
        (hS.map_of_exact (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f))).extClass (zero_add 1) = _
  rw [EtalePullbackGlobalSections.Pro.equiv₀_global, AlgebraicGeometry.FormalGeometry.Completion.ShortExactTransport.Construction.endpointTransport_extClass _ _ _ (hS.map_of_exact (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f))]
  simp only [Iso.refl_inv, Ext.mk₀_id_comp, asIso_hom]
  rw [AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback_apply]
  change _ = ((Ext.mk₀ ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtConstantPullbackIso f).inv.app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).comp
    ((((Sheaf.H.equiv₀ Q terminalIsTerminal).symm z).comp hS.extClass (zero_add 1)).mapExactFunctor
      (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f)) (zero_add 1)).comp
        (Ext.mk₀ (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientPullback ℓ n f)) (add_zero 1)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f) hS]
  simp only [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PresentationPullback
