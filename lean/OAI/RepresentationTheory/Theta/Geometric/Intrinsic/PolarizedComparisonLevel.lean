import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PolarizedComparison

/-! # Polarized Comparison Level -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic

noncomputable section

/-! A constructed native polarized comparison that preserves the
original ordered level gives the full original level-preserving isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {g N : ℕ} {δ : Fin g → ℕ}
    {A B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (D : PolarizedComparison.NativePolarizedComparison A B)

def PolarizedComparison.NativePolarizedComparison.toLevelIso
    (hlevel : ∀ (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (a : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))),
      (A.level.hom.app (.op T) a).val ≫ D.algebraicIso.hom = (B.level.hom.app (.op T) a).val) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A B where
  abelian := D.algebraicIso
  dual := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnderlyingIso.dualFamilyIso A.dual B.dual D.algebraicIso
  abelianGroup := D.algebraicIso_group
  dualGroup := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnderlyingIso.dualFamilyIso_isMonHom A.dual B.dual D.algebraicIso
  polarization := D.algebraicIso_polarization
  poincare := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.PoincareIso.dualFamilyIso_poincare A.dual B.dual D.algebraicIso
  level := hlevel

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic
