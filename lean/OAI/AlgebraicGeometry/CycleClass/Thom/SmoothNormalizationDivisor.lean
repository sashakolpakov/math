import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SmoothLocus
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Pushforward
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.Principal

/-! # Smooth Normalization Divisor -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SmoothNormalizationDivisor.Constructions

noncomputable section

/-! Every actual principal divisor on a singular integral support is the
pushforward of the corresponding divisor on the constructed smooth open
of its finite normalization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Fields.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Field.Constructions
  NormalizationDivisor.Pushforward.Constructions.Local Normalization.SmoothLocus.Constructions.Open RationalOrderTransport.Constructions
  Point.Constructions Open.Principal.Constructions

variable (X : Scheme) [IsIntegral X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

abbrev normalizedSmoothOpen : (Normalization.Scheme.Constructions.normalization X).Opens :=
  Normalization.Scheme.Constructions.normalizationMap X ⁻¹ᵁ Normalization.SmoothLocus.Constructions.Open.normalizationSmoothBase X f

instance normalizedSmoothOpen_nonempty : Nonempty (normalizedSmoothOpen X f) :=
  ⟨⟨genericPoint (Normalization.Scheme.Constructions.normalization X), by
    change Normalization.Scheme.Constructions.normalizationMap X (genericPoint (Normalization.Scheme.Constructions.normalization X)) ∈ Normalization.SmoothLocus.Constructions.Open.normalizationSmoothBase X f
    rw [Normalization.Fields.Constructions.normalizationMap_genericPoint]
    exact Normalization.SmoothLocus.Constructions.Open.normalizationSmoothBase_genericPoint X f⟩⟩

theorem normalizedSmoothOpen_divisorPoint (y : Normalization.Scheme.Constructions.normalization X) (hy : coheight y = 1) :
    y ∈ normalizedSmoothOpen X f :=
  Normalization.SmoothLocus.Constructions.Open.normalizationSmoothBase_divisorPoint X f (Normalization.Scheme.Constructions.normalizationMap X y)
    ((Normalization.Height.Constructions.Local.normalizationMap_coheight X f y).trans hy)

theorem principalDivisor_smoothNormalization_pushforward [AlgebraicGeometry.IsNoetherian X]
    (g : X.functionField) (hg : g ≠ 0) :
    letI := Normalization.Field.Constructions.finiteNormalization_noetherian X f
    Point.Constructions.pointPushforward ((normalizedSmoothOpen X f).ι ≫ Normalization.Scheme.Constructions.normalizationMap X)
      (Point.Constructions.rationalPrincipalPointDivisor (normalizedSmoothOpen X f)
        (RationalOrderTransport.Constructions.openFunctionFieldMap (normalizedSmoothOpen X f).ι
          ((Normalization.Fields.Constructions.normalizationFieldIso X).hom g))) = Point.Constructions.rationalPrincipalPointDivisor X g := by
  let := Normalization.Field.Constructions.finiteNormalization_noetherian X f
  rw [Point.Constructions.pointPushforward_comp, LinearMap.comp_apply,
    Open.Principal.Constructions.principalDivisor_open_pushforward (Normalization.Scheme.Constructions.normalization X) (normalizedSmoothOpen X f)
      (normalizedSmoothOpen_divisorPoint X f)]
  exact NormalizationDivisor.Pushforward.Constructions.Local.normalizationPrincipalDivisor_pushforward X f g hg

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SmoothNormalizationDivisor.Constructions
