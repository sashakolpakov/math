import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Line Trivialization Of -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineTrivializationOf.Construction.LineTrivialization

noncomputable section

/-! Pullback trivializations and line bundles at field-valued points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

universe u

def pullbackIsoOfFactor {X Y : Scheme.{u}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (U : Y.Opens)
    (e : (L.pullback U.ι).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (f : X ⟶ Y) (g : X ⟶ U.toScheme) (h : g ≫ U.ι = f) :
    (L.pullback f).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X :=
  (Scheme.Modules.pullbackCongr h.symm).app L.sheaf ≪≫
    (Scheme.Modules.pullbackComp g U.ι).symm.app L.sheaf ≪≫
    (Scheme.Modules.pullback g).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g

theorem pullback_trivial_over_field {K : Type u} [Field K]
    {Y : Scheme.{u}} (f : Spec (.of K) ⟶ Y) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) :
    Nonempty ((L.pullback f).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of K))) := by
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyTrivial (f (IsLocalRing.closedPoint K))
  have hr : Set.range f ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact (congrArg (fun z => f z ∈ U) (Subsingleton.elim x (IsLocalRing.closedPoint K))).mpr hx
  let g := IsOpenImmersion.lift U.ι f hr
  exact ⟨pullbackIsoOfFactor L U e f g (IsOpenImmersion.lift_fac U.ι f hr)⟩

theorem isAffineOpen_of_subsingleton {X : Scheme.{u}} [IsAffine X] [Subsingleton X]
    (U : X.Opens) : IsAffineOpen U := by
  by_cases h : (U : Set X).Nonempty
  · obtain ⟨x, hx⟩ := h
    have ht : U = ⊤ := top_unique (fun y _ => (Subsingleton.elim y x).symm ▸ hx)
    rw [ht]
    exact isAffineOpen_top X
  · have hb : U = ⊥ := (TopologicalSpace.Opens.not_nonempty_iff_eq_bot U).mp h
    rw [hb]
    exact isAffineOpen_bot X

theorem isAffineHom_from_field {K : Type u} [Field K]
    {Y : Scheme.{u}} (f : Spec (.of K) ⟶ Y) : IsAffineHom f :=
  ⟨fun U _ => isAffineOpen_of_subsingleton (f ⁻¹ᵁ U)⟩

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineTrivializationOf.Construction.LineTrivialization
