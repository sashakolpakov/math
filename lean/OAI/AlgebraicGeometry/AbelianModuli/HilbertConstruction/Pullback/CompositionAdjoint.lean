import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AdjointConjugateNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Composition Adjoint -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.CompositionAdjoint

noncomputable section

/-! The actual scheme-module pullback composition isomorphism is normalized against the composite pullback adjunction. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem pullbackComposition_homEquiv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) {Q : X.Modules}
    (φ : (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f).obj M ⟶ Q) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv M Q
        ((Scheme.Modules.pullbackComp f g).inv.app M ≫ φ) =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f)).homEquiv M Q φ ≫
          (Scheme.Modules.pushforwardComp f g).hom.app Q := by
  have h := AdjointConjugateNormalization.adjunction_homEquiv_precomp_conjugate
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv φ
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.CompositionAdjoint
