import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.TestPolarizationGraphRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.CanonicalDualGroup
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.CanonicalDualPoincare
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PolarizationEnhancement
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.DualTransport

/-! # Graph Power Enhancement Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.GraphPowerEnhancementUniqueness

noncomputable section

/-! Compatible graph-power polarization enhancements of every test of a
fixed Noetherian projective abelian family have the same complete moduli
class. The test scheme and the two chosen duals are unrestricted. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open _root_.CategoryTheory.MonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} [IsNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : Abelian.Schemes.AbelianScheme g S) (PA : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (T : Over S)
variable (l : (A.pullback T.hom).FullLevel N) (L : Line.Bundles.LineBundle (A.pullback T.hom).scheme.left) (d : ℕ)
variable (D E : GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ
  (⟨A.pullback T.hom, l⟩ : Level.Data.AbelianSchemeWithFullLevel g N T.left) L d)
variable (hδ : ∀ i, 0 < δ i) (hd : 0 < d)

def universalGraphPowerEnhancementModuliIso : Moduli.Isomorphisms.LevelPreservingIso D.object E.object := by
  let e := D.dual.uniqueUnderlyingIso E.dual
  letI : IsMonHom e.hom := CanonicalDualGroup.universalCanonicalDual_isMonHom A PA T D.dual E.dual D.polarization E.polarization l hδ
  have hc : Line.Bundles.LineBundle.pullbackClass (e.hom ⊗ₘ 𝟙 (A.pullback T.hom).scheme).left
      (Line.Bundles.LineBundle.classOf E.dual.poincare) = Line.Bundles.LineBundle.classOf D.dual.poincare :=
    CanonicalDualPoincare.universalCanonicalDual_poincare_class A PA T D.dual E.dual
  let C := D.object.withDual E.dual e hc
  have hDE : Line.Bundles.LineBundle.classOf D.object.graphBundle ^ d = Line.Bundles.LineBundle.classOf E.object.graphBundle ^ d := by
    have h : Line.Bundles.LineBundle.classOf (D.object.graphBundle.tensorPower d) =
        Line.Bundles.LineBundle.classOf (E.object.graphBundle.tensorPower d) :=
      Quotient.sound ⟨D.powerIso.some.symm ≪≫ E.powerIso.some⟩
    simpa only [Line.Bundles.LineBundle.classOf_tensorPower] using h
  have hCE : Line.Bundles.LineBundle.classOf C.graphBundle ^ d = Line.Bundles.LineBundle.classOf E.object.graphBundle ^ d :=
    (congrArg (fun v => v ^ d) (D.object.withDual_graphBundle_class E.dual e hc)).trans hDE
  have hp : D.polarization.isogeny.hom ≫ e.hom = E.polarization.isogeny.hom :=
    TestPolarizationGraphRecovery.universalTest_polarization_hom_eq_of_graphPower A PA T E.dual C.polarization E.polarization l hδ d hd hCE
  exact {
    abelian := Iso.refl (A.pullback T.hom).scheme
    dual := e
    abelianGroup := inferInstanceAs (IsMonHom (𝟙 (A.pullback T.hom).scheme))
    dualGroup := inferInstance
    polarization := hp.trans (Category.id_comp _).symm
    poincare := hc
    level := fun _ _ => Category.comp_id _ }

include PA hδ hd in
theorem universalGraphPowerEnhancement_class_unique : D.object.classOf = E.object.classOf :=
  (D.object.classOf_eq_iff E.object).mpr
    ⟨universalGraphPowerEnhancementModuliIso A PA T l L d D E hδ hd⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.GraphPowerEnhancementUniqueness
