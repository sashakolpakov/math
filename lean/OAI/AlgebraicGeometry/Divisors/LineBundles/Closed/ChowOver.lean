import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowPushforward
import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChow

/-! # Chow Over -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowOver.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: closed pushforward with explicit compatibility of structure morphisms -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (h : i ≫ g = f)

def closedDimensionCyclePushforwardOver (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint g d →₀ ℚ) :=
  (CyclePushforward.BundleCycles.closedDimensionCyclePushforward i g d).comp (DimensionChow.BundleCycles.dimensionCycleTransport h.symm d)

theorem closedDimensionCyclePushforwardOver_forget (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion g d (closedDimensionCyclePushforwardOver i f g h d z) =
      Finsupp.mapDomain i (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z) := by
  change Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion g d
    (CyclePushforward.BundleCycles.closedDimensionCyclePushforward i g d (DimensionChow.BundleCycles.dimensionCycleTransport h.symm d z)) = _
  rw [CyclePushforward.BundleCycles.closedDimensionCyclePushforward_forget, DimensionChow.BundleCycles.dimensionCycleTransport_forget]

variable [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    [LocallyOfFiniteType g]

def closedChowPushforwardOver (d : ℕ) : DimensionChow.BundleCycles.DimensionChowQ f d →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ g d :=
  (ChowPushforward.BundleCycles.closedChowPushforward i g d).comp (DimensionChow.BundleCycles.dimensionChowTransport h.symm d)

theorem closedChowPushforwardOver_cycle (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    closedChowPushforwardOver i f g h d (DimensionChow.BundleCycles.dimensionCycleToChowQ f d z) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ g d (closedDimensionCyclePushforwardOver i f g h d z) := by
  change ChowPushforward.BundleCycles.closedChowPushforward i g d
    (DimensionChow.BundleCycles.dimensionChowTransport h.symm d (DimensionChow.BundleCycles.dimensionCycleToChowQ f d z)) = _
  rw [DimensionChow.BundleCycles.dimensionChowTransport_cycle, ChowPushforward.BundleCycles.closedChowPushforward_cycle]
  rfl

end

/-! # LineBundleCycles: genuine Chow transport under isomorphisms of schemes over the complex base -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} (e : X ≅ Y)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (h : e.hom ≫ g = f)

include h in
theorem schemeIso_inverse_over : e.inv ≫ f = g := by
  rw [← h, ← Category.assoc, e.inv_hom_id, Category.id_comp]

theorem schemeIsoCycle_roundtrip (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    closedDimensionCyclePushforwardOver e.inv g f (schemeIso_inverse_over e f g h) d
      (closedDimensionCyclePushforwardOver e.hom f g h d z) = z := by
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective f d
  rw [closedDimensionCyclePushforwardOver_forget, closedDimensionCyclePushforwardOver_forget,
    ← Finsupp.mapDomain_comp]
  have he : (e.inv : Y → X) ∘ (e.hom : X → Y) = id := by
    funext x
    exact congrArg (fun k : X ⟶ X => k x) e.hom_inv_id
  rw [he, Finsupp.mapDomain_id]

variable [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    [LocallyOfFiniteType f] [LocallyOfFiniteType g]

theorem schemeIsoChow_roundtrip (d : ℕ) (a : DimensionChow.BundleCycles.DimensionChowQ f d) :
    closedChowPushforwardOver e.inv g f (schemeIso_inverse_over e f g h) d
      (closedChowPushforwardOver e.hom f g h d a) = a := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d a
  rw [closedChowPushforwardOver_cycle, closedChowPushforwardOver_cycle,
    schemeIsoCycle_roundtrip]

/-- The actual closed pushforwards along an isomorphism and its inverse
give inverse maps on the principal-divisor quotients. -/
def schemeIsoChowEquiv (d : ℕ) : DimensionChow.BundleCycles.DimensionChowQ f d ≃ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ g d :=
  LinearEquiv.ofLinearMap
    (closedChowPushforwardOver e.hom f g h d)
    (closedChowPushforwardOver e.inv g f (schemeIso_inverse_over e f g h) d)
    (by
      ext a
      exact schemeIsoChow_roundtrip e.symm g f (schemeIso_inverse_over e f g h) d a)
    (by
      ext a
      exact schemeIsoChow_roundtrip e f g h d a)

theorem schemeIsoChowEquiv_cycle (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    schemeIsoChowEquiv e f g h d (DimensionChow.BundleCycles.dimensionCycleToChowQ f d z) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ g d (closedDimensionCyclePushforwardOver e.hom f g h d z) :=
  closedChowPushforwardOver_cycle e.hom f g h d z

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowOver.BundleCycles
