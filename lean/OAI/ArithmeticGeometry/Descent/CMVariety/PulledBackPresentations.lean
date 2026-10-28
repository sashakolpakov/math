import OAI.ArithmeticGeometry.Descent.CMVariety.StandardModuli
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.BaseChangeCoherence
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs

/-! # Pulled Back Presentations -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-!
Geometric abelian presentations are transported through the actual
group-preserving comparison between iterated and composite base change.
The represented abelian variety is unchanged by this transport.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs
open scoped _root_.CategoryTheory.MonObj

def StandardModuli.Abelian.ComplexAbelianPresentation.pullbackComp {g : ℕ} {S T : Scheme}
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (f : T ⟶ S) (h : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ T)
    (P : StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback (h ≫ f))) :
    StandardModuli.Abelian.ComplexAbelianPresentation ((G.pullback f).pullback h) where
  variety := P.variety
  comparison := (G.pullbackCompIso f h).symm ≪≫ P.comparison
  comparison_group := by
    change IsMonHom ((G.pullbackCompIso f h).inv ≫ P.comparison.hom)
    infer_instance

def StandardModuli.Abelian.StandardAbelianModuli.pullbackPresentation (M : StandardModuli.Abelian.StandardAbelianModuli)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (j : S.left ⟶ M.space) (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    StandardModuli.Abelian.ComplexAbelianPresentation
      ((M.toArithmeticAbelianModuli.universal.polarized.abelian.pullback j).pullback s.left) :=
  StandardModuli.Abelian.ComplexAbelianPresentation.pullbackComp M.toArithmeticAbelianModuli.universal.polarized.abelian
    j s.left (M.complexFiber (s.left ≫ j))

theorem StandardModuli.Abelian.StandardAbelianModuli.pullbackPresentation_variety (M : StandardModuli.Abelian.StandardAbelianModuli)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (j : S.left ⟶ M.space) (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    (M.pullbackPresentation j s).variety = M.abelianAt (s.left ≫ j) := rfl

end

end OAI.ArithmeticGeometry.Descent.CMVariety
