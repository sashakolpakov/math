import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.TransitionCocycle
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.OpenRestriction

/-! # Cocycle Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.CocycleMaps

noncomputable section

/-! The original inverse-limit maps pull overlap units and their
restricted cocycle equations back on the actual open subschemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {I : Type} [Category.{0} I] (D : I ⥤ Scheme.{0}) (c : Cone D)
    {i : I} {J : Type} (U : J → (D.obj i).Opens)

def openCoefficientsConePullback (k : Over i)
    (r : Open.TransitionCocycle.OpenTransitionCoefficients (fun a => D.map k.hom ⁻¹ᵁ U a)) :
    Open.TransitionCocycle.OpenTransitionCoefficients (fun a => c.π.app i ⁻¹ᵁ U a) :=
  fun a b => Units.map ((opensCone D c i (U a ⊓ U b)).π.app k).appTop.hom.toMonoidHom (r a b)

def openCoefficientsDiagramPullback {k l : Over i} (f : k ⟶ l)
    (r : Open.TransitionCocycle.OpenTransitionCoefficients (fun a => D.map l.hom ⁻¹ᵁ U a)) :
    Open.TransitionCocycle.OpenTransitionCoefficients (fun a => D.map k.hom ⁻¹ᵁ U a) :=
  fun a b => Units.map ((opensDiagram D i (U a ⊓ U b)).map f).appTop.hom.toMonoidHom (r a b)

theorem openTransitionOn_cone (k : Over i)
    (r : Open.TransitionCocycle.OpenTransitionCoefficients (fun a => D.map k.hom ⁻¹ᵁ U a))
    (a b : J) (W : (D.obj i).Opens) (ha : W ≤ U a) (hb : W ≤ U b) :
    Units.map ((opensCone D c i W).π.app k).appTop.hom.toMonoidHom
      (Open.TransitionCocycle.openTransitionOn (fun a => D.map k.hom ⁻¹ᵁ U a) r a b (D.map k.hom ⁻¹ᵁ W)
        ((D.map k.hom).preimage_mono ha) ((D.map k.hom).preimage_mono hb)) =
    Open.TransitionCocycle.openTransitionOn (fun a => c.π.app i ⁻¹ᵁ U a) (openCoefficientsConePullback D c U k r) a b
      (c.π.app i ⁻¹ᵁ W) ((c.π.app i).preimage_mono ha) ((c.π.app i).preimage_mono hb) :=
  OpenRestriction.opensConeUnits_restriction D c (le_inf ha hb) k (r a b)

theorem openTransitionOn_diagram {k l : Over i} (f : k ⟶ l)
    (r : Open.TransitionCocycle.OpenTransitionCoefficients (fun a => D.map l.hom ⁻¹ᵁ U a))
    (a b : J) (W : (D.obj i).Opens) (ha : W ≤ U a) (hb : W ≤ U b) :
    Units.map ((opensDiagram D i W).map f).appTop.hom.toMonoidHom
      (Open.TransitionCocycle.openTransitionOn (fun a => D.map l.hom ⁻¹ᵁ U a) r a b (D.map l.hom ⁻¹ᵁ W)
        ((D.map l.hom).preimage_mono ha) ((D.map l.hom).preimage_mono hb)) =
    Open.TransitionCocycle.openTransitionOn (fun a => D.map k.hom ⁻¹ᵁ U a) (openCoefficientsDiagramPullback D U f r) a b
      (D.map k.hom ⁻¹ᵁ W) ((D.map k.hom).preimage_mono ha) ((D.map k.hom).preimage_mono hb) :=
  OpenRestriction.opensDiagramUnits_restriction D (le_inf ha hb) f (r a b)

theorem openCoefficientsConePullback_diagram {k l : Over i} (f : k ⟶ l)
    (r : Open.TransitionCocycle.OpenTransitionCoefficients (fun a => D.map l.hom ⁻¹ᵁ U a)) :
    openCoefficientsConePullback D c U k (openCoefficientsDiagramPullback D U f r) =
      openCoefficientsConePullback D c U l r := by
  funext a b
  apply Units.ext
  exact InverseLimit.Units.coneSection_map (opensDiagram D i (U a ⊓ U b)) (opensCone D c i (U a ⊓ U b)) f (r a b).val

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.CocycleMaps
