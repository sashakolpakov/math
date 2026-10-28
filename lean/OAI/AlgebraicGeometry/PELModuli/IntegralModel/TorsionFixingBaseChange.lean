import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.TorsionBaseChange

/-! # Torsion Fixing Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.TorsionFixingBaseChange

noncomputable section

/-! Fixing the actual torsion inclusion commutes with arbitrary base
change, using the proved isomorphism of the two torsion kernels. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem fixes_torsion_baseChange_iff
    {S T : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (f : T ⟶ S) (n : ℕ) (u : A.scheme ⟶ A.scheme) :
    (Over.pullback f).map (A.torsionInclusion n ≫ u) =
        (Over.pullback f).map (A.torsionInclusion n) ↔
      (A.pullback f).torsionInclusion n ≫ (Over.pullback f).map u =
        (A.pullback f).torsionInclusion n := by
  let e := AbelianScheme.FrobeniusKernel.TorsionBaseChange.Construction.torsionSchemeBaseChangeIso A f n
  have he : e.hom ≫ (A.pullback f).torsionInclusion n =
      (Over.pullback f).map (A.torsionInclusion n) :=
    AbelianScheme.FrobeniusKernel.TorsionBaseChange.Construction.torsionSchemeBaseChangeIso_inclusion A f n
  rw [Functor.map_comp, ← he, Category.assoc]
  exact cancel_epi e.hom

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.TorsionFixingBaseChange
