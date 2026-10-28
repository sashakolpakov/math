import OAI.AlgebraicGeometry.Picard.PoincareBundle.PositiveFormulaIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.AffinePullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointLineBundleTriviality
import OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemePullback

/-! # Positive Formula Affine Square -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.PositiveFormulaAffineSquare

noncomputable section

/-! A normalized positive formula pulls back through an actual affine comparison of field groups and their product squares. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

/-- The native inverse-image comparison associated with a commuting square. -/
def squareIso {W X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (c : X ⟶ W) (d : W ⟶ Z) (h : a ≫ b = c ≫ d) (M : Z.Modules) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj M) ≅
      (Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback d).obj M) :=
  (Scheme.Modules.pullbackComp a b).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M ≪≫
    (Scheme.Modules.pullbackComp c d).symm.app M

variable {k K : Type u} [Field k] [Field K]
  (A : Over (Spec (.of k))) [GrpObj A] (B : Over (Spec (.of K))) [GrpObj B]
  (q : B.left ⟶ A.left) [IsAffineHom q] (r : (B ⊗ B).left ⟶ (A ⊗ A).left)
  (h1 : r ≫ (fst A A).left = (fst B B).left ≫ q)
  (h2 : r ≫ (snd A A).left = (snd B B).left ≫ q)
  (hm : r ≫ μ[A].left = μ[B].left ≫ q)
  (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (R : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (B ⊗ B).left)
  (eQ : R.sheaf ≅ (Scheme.Modules.pullback r).obj Q.sheaf)

include h1 h2 hm eQ

/-- Affine pullback preserves ampleness and the actual tensor formula; the target field supplies its identity frame. -/
theorem positive (hp : AbelianScheme.IsogenyQuotient.PositiveFormula.Construction.PositivePoincareFormula A Q) : AbelianScheme.IsogenyQuotient.PositiveFormula.Construction.PositivePoincareFormula B R := by
  obtain ⟨L, hL, _, ⟨e⟩⟩ := hp
  let L' := L.pullback q
  refine ⟨L', hL.pullback_of_isAffineHom q, ?_, ⟨?_⟩⟩
  · have : Subsingleton (𝟙_ (Over (Spec (.of K)))).left := inferInstanceAs (Subsingleton (Spec (.of K)))
    have : Nonempty (𝟙_ (Over (Spec (.of K)))).left := inferInstanceAs (Nonempty (Spec (.of K)))
    exact (L'.pullback η[B].left).exists_trivialization_of_subsingleton
  · let M := (L.pullback (fst A A).left).sheaf
    let N := (L.pullback (snd A A).left).sheaf
    let e1 := squareIso (fst B B).left q r (fst A A).left h1.symm L.sheaf
    let e2 := squareIso (snd B B).left q r (snd A A).left h2.symm L.sheaf
    exact AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr
        (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr eQ e1 ≪≫ (Homomorphisms.SchemePullback.Construction.tensorModuleArbitraryPullbackIso r Q.sheaf M).symm) e2 ≪≫
      (Homomorphisms.SchemePullback.Construction.tensorModuleArbitraryPullbackIso r (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf M) N).symm ≪≫
      (Scheme.Modules.pullback r).mapIso e ≪≫ squareIso r μ[A].left μ[B].left q hm L.sheaf

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.PositiveFormulaAffineSquare
