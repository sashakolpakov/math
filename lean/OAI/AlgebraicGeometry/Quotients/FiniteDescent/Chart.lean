import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GlobalQuotientOf
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.QuotientTransitionsOpen

/-! # Chart -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.Chart.Construction.ChartQuotients

/-!
# Gluing local quotients without supplied quotient transitions

Only the local quotients and their kernel pairs are input data. The transition
maps, their functor laws, and the cartesian quotient diagram are constructed
by effective descent and uniqueness.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

/-- Local quotient data on an open cover. The relation chart is the source
restriction of the original relation, with target in the same object chart. -/
structure Data {R X : Scheme.{u}} (s t : R ⟶ X) (𝒰 : X.OpenCover) where
  quotient : 𝒰.I₀ → Scheme.{u}
  projection : ∀ i, 𝒰.X i ⟶ quotient i
  finite : ∀ i, IsFinite (projection i)
  flat : ∀ i, Flat (projection i)
  finitelyPresented : ∀ i, LocallyOfFinitePresentation (projection i)
  surjective : ∀ i, Surjective (projection i)
  relation : 𝒰.I₀ → Scheme.{u}
  inclusion : ∀ i, relation i ⟶ R
  source : ∀ i, relation i ⟶ 𝒰.X i
  target : ∀ i, relation i ⟶ 𝒰.X i
  source_isPullback : ∀ i, IsPullback (source i) (inclusion i) (𝒰.f i) s
  target_comp : ∀ i, target i ≫ 𝒰.f i = inclusion i ≫ t
  kernelPair : ∀ i, IsKernelPair (projection i) (source i) (target i)

namespace Data

variable {R X : Scheme.{u}} {s t : R ⟶ X} {𝒰 : X.OpenCover} (d : Data s t 𝒰)

instance (i : 𝒰.I₀) : IsFinite (d.projection i) := d.finite i
instance (i : 𝒰.I₀) : Flat (d.projection i) := d.flat i
instance (i : 𝒰.I₀) : LocallyOfFinitePresentation (d.projection i) := d.finitelyPresented i
instance (i : 𝒰.I₀) : Surjective (d.projection i) := d.surjective i

variable [Category.{v} 𝒰.I₀] [𝒰.LocallyDirected]

/-- The transition between source restrictions of the relation. -/
noncomputable def relationMap {i j : 𝒰.I₀} (f : i ⟶ j) : d.relation i ⟶ d.relation j :=
  (d.source_isPullback j).lift (d.source i ≫ 𝒰.trans f) (d.inclusion i) (by
    rw [Category.assoc, 𝒰.trans_map, (d.source_isPullback i).w])

@[reassoc (attr := simp)]
theorem relationMap_source {i j : 𝒰.I₀} (f : i ⟶ j) :
    d.relationMap f ≫ d.source j = d.source i ≫ 𝒰.trans f :=
  (d.source_isPullback j).lift_fst _ _ _

@[reassoc (attr := simp)]
theorem relationMap_inclusion {i j : 𝒰.I₀} (f : i ⟶ j) :
    d.relationMap f ≫ d.inclusion j = d.inclusion i :=
  (d.source_isPullback j).lift_snd _ _ _

theorem relationMap_isPullback {i j : 𝒰.I₀} (f : i ⟶ j) :
    IsPullback (d.source i) (d.relationMap f) (𝒰.trans f) (d.source j) := by
  apply IsPullback.of_bot _ (d.relationMap_source f).symm (d.source_isPullback j)
  simpa only [d.relationMap_inclusion, 𝒰.trans_map] using d.source_isPullback i

theorem relationMap_target {i j : 𝒰.I₀} (f : i ⟶ j) :
    d.target i ≫ 𝒰.trans f = d.relationMap f ≫ d.target j := by
  apply (cancel_mono (𝒰.f j)).mp
  simp only [Category.assoc, 𝒰.trans_map, d.target_comp, d.relationMap_inclusion_assoc]

theorem existsUnique_transition {i j : 𝒰.I₀} (f : i ⟶ j) :
    ∃! g : d.quotient i ⟶ d.quotient j,
      d.projection i ≫ g = 𝒰.trans f ≫ d.projection j ∧ IsOpenImmersion g ∧
      IsPullback (d.projection i) (𝒰.trans f) g (d.projection j) := by
  have : IsOpenImmersion (𝒰.trans f) := 𝒰.property_trans f
  exact QuotientTransitionsOpen.Construction.QuotientTransitions.existsUnique_open_transition
    (d.projection j) (d.kernelPair j) (𝒰.trans f) (d.relationMap f)
    (d.source i) (d.target i) (d.relationMap_isPullback f) (d.relationMap_target f)
    (d.projection i) (d.kernelPair i)

/-- The canonical map between quotient charts. -/
noncomputable def transition {i j : 𝒰.I₀} (f : i ⟶ j) : d.quotient i ⟶ d.quotient j :=
  (d.existsUnique_transition f).choose

theorem transition_properties {i j : 𝒰.I₀} (f : i ⟶ j) :
    d.projection i ≫ d.transition f = 𝒰.trans f ≫ d.projection j ∧
    IsOpenImmersion (d.transition f) ∧
    IsPullback (d.projection i) (𝒰.trans f) (d.transition f) (d.projection j) :=
  (d.existsUnique_transition f).choose_spec.1

@[reassoc (attr := simp)]
theorem transition_fac {i j : 𝒰.I₀} (f : i ⟶ j) :
    d.projection i ≫ d.transition f = 𝒰.trans f ≫ d.projection j :=
  (d.transition_properties f).1

instance {i j : 𝒰.I₀} (f : i ⟶ j) : IsOpenImmersion (d.transition f) :=
  (d.transition_properties f).2.1

/-- The quotient diagram; its identity and composition laws follow from
epimorphic local quotient projections. -/
noncomputable def functor : 𝒰.I₀ ⥤ Scheme.{u} where
  obj := d.quotient
  map := d.transition
  map_id i := by
    apply (cancel_epi (d.projection i)).mp
    rw [d.transition_fac, 𝒰.trans_id, Category.id_comp, Category.comp_id]
  map_comp f g := by
    apply (cancel_epi (d.projection _)).mp
    rw [d.transition_fac, ← Category.assoc, d.transition_fac, Category.assoc,
      d.transition_fac, ← Category.assoc, ← 𝒰.trans_comp]

/-- The local quotient projections form a natural transformation. -/
noncomputable def natTrans : 𝒰.functorOfLocallyDirected ⟶ d.functor where
  app := d.projection
  naturality _ _ f := (d.transition_fac f).symm

theorem equifibered : d.natTrans.Equifibered := fun {_ _} f =>
  (d.transition_properties f).2.2.flip

instance {i j : 𝒰.I₀} (f : i ⟶ j) : IsOpenImmersion (d.functor.map f) :=
  inferInstanceAs (IsOpenImmersion (d.transition f))

include d in
/-- Local quotient data alone suffice to build the global quotient. -/
theorem exists_quotient [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] :
    ∃ (Q : Scheme.{u}) (π : X ⟶ Q),
      IsFinite π ∧ Flat π ∧ LocallyOfFinitePresentation π ∧ Surjective π ∧
      IsKernelPair π s t ∧
      ∀ (T : Scheme.{u}) (f : X ⟶ T), s ≫ f = t ≫ f →
        ∃! g : Q ⟶ T, π ≫ g = f :=
  GlobalQuotientOf.Construction.GlobalQuotient.exists_of_cartesian_charts s t 𝒰 d.functor d.natTrans d.equifibered
    d.finite d.flat d.finitelyPresented d.surjective d.relation d.inclusion
    d.source d.target d.source_isPullback d.target_comp d.kernelPair

end Data

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.Chart.Construction.ChartQuotients
