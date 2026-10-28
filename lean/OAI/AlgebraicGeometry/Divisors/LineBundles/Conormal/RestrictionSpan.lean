import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.ConormalLocalization
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.SymmetricDiagram

/-! # Restriction Span -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.RestrictionSpan.BundleCycles

noncomputable section

/-! Conormal restriction maps on the affine Zariski site generate the
target module over its actual quotient coefficient ring. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (I : X.IdealSheafData)

theorem conormalRestriction_span {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    Submodule.span (Γ(X, U.1) ⧸ I.ideal U)
      (Set.range (ConormalRestriction.BundleCycles.cotangentCoefficientMap (I.ideal V) (I.ideal U)
        (X.presheaf.map ((toOpensFunctor X).map i).op).hom
        (I.ideal_le_comap_ideal (toOpens_mono i.le)))) = ⊤ := by
  obtain ⟨r, hr⟩ := i.le
  have hU : V.basicOpen r = U := Subtype.ext hr
  subst U
  let S := Γ(X, (V.basicOpen r).1)
  let φ : Γ(X, V.1) →+* S := (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  let : Algebra Γ(X, V.1) S := φ.toAlgebra
  let : IsLocalization.Away r S := V.2.isLocalization_basicOpen r
  exact Augmented.ConormalLocalization.BundleCycles.cotangentCoefficientMap_span (I.ideal V) S (Submonoid.powers r)
    (I.ideal (V.basicOpen r)) (I.map_ideal_basicOpen V r)
    (I.ideal_le_comap_ideal (X.basicOpen_le r))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.RestrictionSpan.BundleCycles
