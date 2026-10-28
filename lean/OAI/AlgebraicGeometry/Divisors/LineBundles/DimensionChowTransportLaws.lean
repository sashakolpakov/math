import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowOver

/-! # Dimension Chow Transport Laws -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChowTransportLaws.BundleCycles

noncomputable section

/-! # LineBundleCycles: inverse and pushforward laws for actual structure-map transport on Chow groups -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] {f g : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}

theorem dimensionChowTransport_inverse (h : f = g) (d : ℕ) (a : DimensionChow.BundleCycles.DimensionChowQ f d) :
    DimensionChow.BundleCycles.dimensionChowTransport h.symm d (DimensionChow.BundleCycles.dimensionChowTransport h d a) = a := by
  subst g
  rfl

theorem dimensionChowTransport_injective (h : f = g) (d : ℕ) :
    Function.Injective (DimensionChow.BundleCycles.dimensionChowTransport h d) := by
  subst g
  exact Function.injective_id

theorem dimensionChowTransport_surjective (h : f = g) (d : ℕ) :
    Function.Surjective (DimensionChow.BundleCycles.dimensionChowTransport h d) := by
  subst g
  exact Function.surjective_id

theorem closedChowPushforwardOver_transport {Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y]
    (i : X ⟶ Y) [IsClosedImmersion i] (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType g]
    (h : i ≫ g = f) (d : ℕ) (a : DimensionChow.BundleCycles.DimensionChowQ (i ≫ g) d) :
    Closed.ChowOver.BundleCycles.closedChowPushforwardOver i f g h d (DimensionChow.BundleCycles.dimensionChowTransport h d a) =
      Closed.ChowPushforward.BundleCycles.closedChowPushforward i g d a := by
  change Closed.ChowPushforward.BundleCycles.closedChowPushforward i g d
    (DimensionChow.BundleCycles.dimensionChowTransport h.symm d (DimensionChow.BundleCycles.dimensionChowTransport h d a)) = _
  rw [dimensionChowTransport_inverse]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChowTransportLaws.BundleCycles
