import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementParameterPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementTransportIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ParameterPullbackCoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackLevelCoherence

/-! # Enhancement Parameter Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Pulling an enhancement along a parameter morphism preserves its
complete original moduli class, including the ordered full level. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable {F : Level.Data.AbelianSchemeWithFullLevel g N S} {L : Line.Bundles.LineBundle F.abelian.scheme.left} {d : ℕ}
variable {U T : Over S}
variable (D : GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback T.hom)
  (L.pullback (CategoryTheory.Limits.pullback.fst F.abelian.scheme.hom T.hom)) d) (f : U ⟶ T)

def GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement.parameterPullbackModuliIso :
    Moduli.Isomorphisms.LevelPreservingIso (D.object.pullback f.left) (D.parameterPullback f).object := by
  let e : ((F.pullback T.hom).pullback f.left).abelian.scheme ≅
      (F.pullback U.hom).abelian.scheme := (F.abelian.parameterPullbackIso f).symm
  letI : IsMonHom e.hom := Abelian.Schemes.AbelianScheme.parameterPullbackIso_symm_isMonHom f F.abelian
  exact (D.pullback f.left).transportFamilyModuliIso (G := F.pullback U.hom)
    (M := L.pullback (CategoryTheory.Limits.pullback.fst F.abelian.scheme.hom U.hom)) e
    (Quotient.sound ⟨Line.Bundles.LineBundle.parameterInversePullbackIso F.abelian.scheme L f⟩)
    (Abelian.Schemes.AbelianScheme.FullLevel.transport_parameterPullback F.abelian f F.level)

theorem GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement.parameterPullback_object_class :
    (D.parameterPullback f).object.classOf = Moduli.Isomorphisms.PolarizedLevelClasses.pullback f.left D.object.classOf :=
  ((D.object.pullback f.left).classOf_eq_iff (D.parameterPullback f).object).mpr
    ⟨D.parameterPullbackModuliIso f⟩ |>.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
