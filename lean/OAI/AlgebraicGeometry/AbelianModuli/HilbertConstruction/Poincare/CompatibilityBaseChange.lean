import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseChange

/-! # Compatibility Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.CompatibilityBaseChange

noncomputable section

/-! Compatibility with actual Poincare line-bundle classes survives arbitrary base change independently of polarization and full-level equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

theorem poincareCompatibility_pullback
    {S T : Scheme.{u}} {g : ℕ} {A B : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (E : Dual.Data.DualAbelianData B)
    (d : D.abelian.scheme ⟶ E.abelian.scheme) (e : A.scheme ⟶ B.scheme)
    (h : Line.Bundles.LineBundle.pullbackClass (d ⊗ₘ e).left (Line.Bundles.LineBundle.classOf E.poincare) = Line.Bundles.LineBundle.classOf D.poincare)
    (b : T ⟶ S) :
    Line.Bundles.LineBundle.pullbackClass ((Over.pullback b).map d ⊗ₘ (Over.pullback b).map e).left
      (Line.Bundles.LineBundle.classOf (E.pullback b).poincare) = Line.Bundles.LineBundle.classOf (D.pullback b).poincare :=
  (Line.Bundles.LineBundle.pullbackClass_comp ((Over.pullback b).map d ⊗ₘ (Over.pullback b).map e).left
    (E.poincarePullbackOverMap b).left (Line.Bundles.LineBundle.classOf E.poincare)).symm.trans
      ((congrArg (fun z => Line.Bundles.LineBundle.pullbackClass z (Line.Bundles.LineBundle.classOf E.poincare))
        (Moduli.BaseChange.poincarePullbackOverMap_naturality D E d e b)).trans
        ((Line.Bundles.LineBundle.pullbackClass_comp (D.poincarePullbackOverMap b).left (d ⊗ₘ e).left
          (Line.Bundles.LineBundle.classOf E.poincare)).trans
          (congrArg (Line.Bundles.LineBundle.pullbackClass (D.poincarePullbackOverMap b).left) h)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.CompatibilityBaseChange
