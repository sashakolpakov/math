import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.CartierGenericPoint
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GenericClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportDimension

/-! # Immersion Codimension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.ImmersionCodimension.BundleCycles

noncomputable section

/-! The actual principal image ideal gives codimension one for an integral closed fiber, hence the native analytic dimension equality. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem integralPrincipalImmersion_dimension {Y X : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] (i : Y ⟶ X) [IsClosedImmersion i]
    (hi : Cartier.IdealBundle.Cycles.HasRegularPrincipalImageIdeals i) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ f) + 1 = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by
  have h := DivisorClass.Chern.SupportCodimension.Construction.pointClosure_dimension_add_one f (i (genericPoint Y))
    (Integral.CartierGenericPoint.BundleCycles.integralCartier_genericPoint_coheight i hi)
  rw [Point.SupportDimension.BundleCycles.pointClosure_dimension_closedImmersion, LineBundle.GenericClass.Cycles.genericPointSupport_dimension] at h
  exact h

theorem integralPrincipalImmersion_nativeCodimension {Y X : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    [IsIntegral X.left] [IsIntegral Y.left] [AlgebraicGeometry.IsNoetherian X.left]
    [LocallyOfFiniteType X.hom] (i : Y ⟶ X) [IsClosedImmersion i.left]
    (hi : Cartier.IdealBundle.Cycles.HasRegularPrincipalImageIdeals i.left) :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom + 1 =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom := by
  let : LocallyOfFiniteType Y.hom := i.w ▸ inferInstanceAs (LocallyOfFiniteType (i.left ≫ X.hom))
  have h := integralPrincipalImmersion_dimension i.left hi X.hom
  rw [i.w, Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension,
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension] at h
  exact h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.ImmersionCodimension.BundleCycles
