import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Integral
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.RankOneProjective
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GenericClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberFieldNaturality

/-! # Has -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Has.BundleCycles

noncomputable section

/-! The actual symmetric projective line and its dimension-one
affine source charts over the coefficient spectrum. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R : Type) [CommRing R]

def symmetricProjectiveLineBasis : Module.Basis (Unit ⊕ Unit) R (R × R) :=
  (Module.Basis.singleton Unit R).prod (Module.Basis.singleton Unit R)

theorem symmetricProjectiveLine_hasSourceCharts :
    AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (Scheme.BundleCycles.symmetricProjectiveToBase R (R × R)) 1 := by
  have h := Symmetric.BasisAffineChart.BundleCycles.symmetricProjective_hasAffineSpaceSourceChartsOfRank (symmetricProjectiveLineBasis R)
  have hc : Nat.card (Unit ⊕ Unit) - 1 = 1 := by simp [Nat.card_eq_fintype_card]
  exact hc ▸ h

instance symmetricProjectiveLine_geometricallyIntegral :
    GeometricallyIntegral (Scheme.BundleCycles.symmetricProjectiveToBase R (R × R)) :=
  IntegralFibers.BundleCycles.symmetricProjective_geometricallyIntegral (symmetricProjectiveLineBasis R)

instance symmetricRankOneProjective_isIntegral [IsDomain R] :
    IsIntegral (Scheme.BundleCycles.symmetricProjectiveScheme R R) :=
  IsIntegral.of_isIso (inv (Scheme.BundleCycles.symmetricProjectiveToBase R R))

instance symmetricProjectiveLine_isIntegral [IsNoetherianRing R] [IsDomain R] :
    IsIntegral (Scheme.BundleCycles.symmetricProjectiveScheme R (R × R)) :=
  Integral.BundleCycles.symmetricProjective_isIntegral_of_basis R (R × R) (symmetricProjectiveLineBasis R)

theorem symmetricProjectiveLine_dimension [IsNoetherianRing R] [IsDomain R]
    (f : Spec (.of R) ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Scheme.BundleCycles.symmetricProjectiveToBase R (R × R) ≫ f) =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f + 1 := by
  have h := AffineSpace.SourceRank.BundleCycles.affineSpaceSourceFiberGenericPoint_dimension (Scheme.BundleCycles.symmetricProjectiveToBase R (R × R)) f 1
    (symmetricProjectiveLine_hasSourceCharts R) (genericPoint (Spec (.of R)))
  rw [Integral.FiberFieldNaturality.BundleCycles.integralFiberGenericPoint_generic, LineBundle.GenericClass.Cycles.genericPointSupport_dimension, LineBundle.GenericClass.Cycles.genericPointSupport_dimension] at h
  exact h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Has.BundleCycles
