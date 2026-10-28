import OAI.AlgebraicGeometry.Divisors.LineBundles.Chow
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.Chow

/-! # Map Characterization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.MapCharacterization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: geometric characterizations of the maps whose existence is asserted

The class map is fixed on every actual finite geometric cycle. The projection
and normal-bundle maps are fixed on every representative by genuine fiber
cycles. All dimension grades are retained, so no common component dimension
or constant global normal rank is imposed. Graph pullback is specified by
normal-bundle extension followed by actual deformation specialization.
No Betti pullback compatibility is included in these predicates.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

def IsGeometricCycleClass (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (cl : Chow.BundleCycles.ChowQ X p ⟶ X.rationalCohomology (p + p)) : Prop :=
  ∀ z : X.RationalDimensionCycle p, cl (Chow.BundleCycles.cycleToChowQ X p z) = X.geometricCycleClassMap p z

abbrev GraphProjectionChowFamily {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) (p : ℕ) :=
  ∀ d : ℕ, Chow.BundleCycles.ChowQ Y p →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ (Graph.Chow.BundleCycles.graphAmbientStructureMap f) d

abbrev GraphNormalChowFamily {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) (p : ℕ) :=
  ∀ d : ℕ, Chow.BundleCycles.ChowQ X p →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ (Graph.Chow.BundleCycles.graphConeStructureMap f) d

def IsGraphProjectionChowFamily {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) (p : ℕ)
    (pr : GraphProjectionChowFamily f p) : Prop :=
  ∀ (d : ℕ) (z : Y.RationalDimensionCycle p),
    pr d (Chow.BundleCycles.cycleToChowQ Y p z) = Point.CycleChow.BundleCycles.pointCycleToChowQ (Graph.Chow.BundleCycles.graphAmbientStructureMap f) d
      (Graph.Chow.BundleCycles.graphProjectionPointPullback f (Chow.BundleCycles.pointCycle Y p z))

def IsGraphNormalChowFamily {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) (p : ℕ)
    (normal : GraphNormalChowFamily f p) : Prop :=
  ∀ (d : ℕ) (z : X.RationalDimensionCycle p),
    normal d (Chow.BundleCycles.cycleToChowQ X p z) = Point.CycleChow.BundleCycles.pointCycleToChowQ (Graph.Chow.BundleCycles.graphConeStructureMap f) d
      (Graph.Chow.BundleCycles.graphNormalPointPullback f (Chow.BundleCycles.pointCycle X p z))

/-- The defining graph equation is `π* (pull α) = σΓ (prY* α)` in every
actual dimension grade. The quantified auxiliary maps must descend the
displayed geometric cycle formulas, and normal extension must be jointly
injective across the grades. Their existence is part of the assertion. -/
def IsGeometricGraphPullback {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) (p : ℕ)
    (pull : Chow.BundleCycles.ChowQ Y p ⟶ Chow.BundleCycles.ChowQ X p) : Prop :=
  ∃ (pr : GraphProjectionChowFamily f p) (normal : GraphNormalChowFamily f p),
    IsGraphProjectionChowFamily f p pr ∧ IsGraphNormalChowFamily f p normal ∧
      Function.Injective (fun a : Chow.BundleCycles.ChowQ X p => fun d : ℕ => normal d a) ∧
      ∀ (a : Chow.BundleCycles.ChowQ Y p) (d : ℕ), normal d (pull a) =
        Global.ChowSpecialization.BundleCycles.globalChowSpecialization (Graph.OpenAmbient.BundleCycles.graph f).ker (Graph.Chow.BundleCycles.graphAmbientStructureMap f) d (pr d a)

theorem isGeometricCycleClass_unique (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (a b : Chow.BundleCycles.ChowQ X p ⟶ X.rationalCohomology (p + p))
    (ha : IsGeometricCycleClass X p a) (hb : IsGeometricCycleClass X p b) : a = b := by
  apply ModuleCat.hom_ext
  ext c
  obtain ⟨z, rfl⟩ := Chow.BundleCycles.cycleToChowQ_surjective X p c
  exact (ha z).trans (hb z).symm

theorem isGraphProjectionChowFamily_unique {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (p : ℕ) (a b : GraphProjectionChowFamily f p)
    (ha : IsGraphProjectionChowFamily f p a) (hb : IsGraphProjectionChowFamily f p b) : a = b := by
  funext d
  ext c
  obtain ⟨z, rfl⟩ := Chow.BundleCycles.cycleToChowQ_surjective Y p c
  exact (ha d z).trans (hb d z).symm

theorem isGraphNormalChowFamily_unique {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (p : ℕ) (a b : GraphNormalChowFamily f p)
    (ha : IsGraphNormalChowFamily f p a) (hb : IsGraphNormalChowFamily f p b) : a = b := by
  funext d
  ext c
  obtain ⟨z, rfl⟩ := Chow.BundleCycles.cycleToChowQ_surjective X p c
  exact (ha d z).trans (hb d z).symm

theorem isGeometricGraphPullback_unique {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (p : ℕ) (a b : Chow.BundleCycles.ChowQ Y p ⟶ Chow.BundleCycles.ChowQ X p)
    (ha : IsGeometricGraphPullback f p a) (hb : IsGeometricGraphPullback f p b) : a = b := by
  obtain ⟨pa, na, hpa, hna, hia, hga⟩ := ha
  obtain ⟨pb, nb, hpb, hnb, _, hgb⟩ := hb
  have hp := isGraphProjectionChowFamily_unique f p pa pb hpa hpb
  have hn := isGraphNormalChowFamily_unique f p na nb hna hnb
  subst pb
  subst nb
  apply ModuleCat.hom_ext
  ext c
  apply hia
  funext d
  exact (hga c d).trans (hgb c d).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.MapCharacterization.BundleCycles
