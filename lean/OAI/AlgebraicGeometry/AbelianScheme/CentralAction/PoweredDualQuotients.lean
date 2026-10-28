import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PoweredQuotients
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.DualQuotientPolarization
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ScalarDual
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.QuotientPoincarePullback

/-! # Powered Dual Quotients -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PoweredDualQuotients

noncomputable section

/-! The dual of each geometric scalar quotient is an actual group
isomorphism preserving the polarization, with a raw Poincare comparison
after pullback by the actual isogeny. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.NumberField
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

variable {E K : Type} [Field E] [NumberField E] [IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]

theorem fiberScalarIsogeny_dual_finite_etale_surjective
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (hgeometry : D.HasIntegralModelGeometry)
    (β : 𝓞 E) (n : ℕ) (hn : n ≠ 0)
    (hnorm : β * IsCMField.ringOfIntegersComplexConj E β = n)
    (hmark : Marking.Construction.levelReduction E D.level β = 1)
    {k : Type} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ Spec (.of K))
    (x : D.GeometricPoint b) :
    IsFinite (PoweredQuotients.Construction.fiberScalarIsogeny D hgeometry β n hn hnorm hmark b x).dualHom.left ∧
    Etale (PoweredQuotients.Construction.fiberScalarIsogeny D hgeometry β n hn hnorm hmark b x).dualHom.left ∧
    Surjective (PoweredQuotients.Construction.fiberScalarIsogeny D hgeometry β n hn hnorm hmark b x).dualHom.left := by
  let f := ScalarIsogeny.Construction.scalarPELIsogeny_of_norm D.family D.space.hom
    (GenericModuli.Construction.generic_family_rosati D hgeometry) β n hn hnorm hmark
  have hf := ScalarDual.Construction.scalarIsogeny_dual_finite_etale_surjective D.family D.space.hom
    (GenericModuli.Construction.generic_family_rosati D hgeometry) β hn hnorm f rfl
  exact ⟨MorphismProperty.overPullbackMap x.left f.dualHom hf.1,
    MorphismProperty.overPullbackMap x.left f.dualHom hf.2.1,
    MorphismProperty.overPullbackMap x.left f.dualHom hf.2.2⟩

/-- The constructed scalar quotient's dual group law and polarization
follow on the actual fibers, without adding geometric compatibility inputs. -/
theorem fiber_scalar_quotient_dual_polarization
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (hgeometry : D.HasIntegralModelGeometry)
    (β : 𝓞 E) (n : ℕ) (hn : n ≠ 0)
    (hnorm : β * IsCMField.ringOfIntegersComplexConj E β = n)
    (hmark : Marking.Construction.levelReduction E D.level β = 1)
    {k : Type} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ Spec (.of K))
    (x y : D.GeometricPoint b)
    (f : TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b y) n)
    (j : (D.fiberFamily b y).abelian.scheme ≅ (D.fiberFamily b x).abelian.scheme)
    [IsMonHom j.hom] (hj : f.isogeny.hom ≫ j.hom = Scalar.Construction.scalarMap (D.fiberFamily b x) β) :
    DualQuotientPolarization.Construction.QuotientDualCompatible (D.fiberFamily b x) (D.fiberFamily b y) j := by
  let g := PoweredQuotients.Construction.fiberScalarIsogeny D hgeometry β n hn hnorm hmark b x
  have hg := fiberScalarIsogeny_dual_finite_etale_surjective
    D hgeometry β n hn hnorm hmark b x
  have hfac : f.isogeny.hom ≫ j.hom = g.isogeny.hom :=
    hj.trans (PoweredQuotients.Construction.fiberScalarIsogeny_hom D hgeometry β n hn hnorm hmark b x).symm
  have h := @DualQuotientPolarization.Construction.dual_quotient_group_polarization k (𝓞 E) _ _ (3 * s) D.level n
    (D.fiberFamily b x) (D.fiberFamily b y) f g j ‹IsMonHom j.hom› hfac hg.1 hg.2.1
  exact h

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PoweredDualQuotients
