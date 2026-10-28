import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveTriviality
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Open Frame -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenFrame.Construction.OpenFrameFibers

noncomputable section

/-! A frame on the inverse image of an open set trivializes every fiber
over that open set. Neighborhood frames therefore make the fiber locus open. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable {X Y : Scheme.{u}} (M : X.Modules) (U : X.Opens)

def pullbackIso (f : Y ⟶ X) (hf : Set.range f ⊆ Set.range U.ι)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) :
    (Scheme.Modules.pullback f).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y :=
  let j := IsOpenImmersion.lift U.ι f hf
  (Scheme.Modules.pullbackCongr (IsOpenImmersion.lift_fac U.ι f hf).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp j U.ι).app M).symm ≪≫
    (Scheme.Modules.pullback j).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso j

variable {S : Scheme.{u}} (π : X ⟶ S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)

theorem fiber_range (V : S.Opens) (x : S) (hx : x ∈ V) :
    Set.range (π.fiberι x) ⊆ Set.range (π ⁻¹ᵁ V).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨z, rfl⟩
  change π (π.fiberι x z) ∈ V
  rw [← Scheme.Hom.comp_apply, π.fiber_fac x, Scheme.Hom.comp_apply,
    Scheme.fromSpecResidueField_apply]
  exact hx

def fiberIso (V : S.Opens) (x : S) (hx : x ∈ V)
    (e : (L.pullback (π ⁻¹ᵁ V).ι).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π ⁻¹ᵁ V).toScheme) :
    (L.pullback (π.fiberι x)).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π.fiber x) :=
  pullbackIso L.sheaf (π ⁻¹ᵁ V) (π.fiberι x) (fiber_range π V x hx) e

theorem isOpen_of_neighborhoods
    (hn : ∀ x ∈ ProjectiveTriviality.Construction.ProjectiveTrivialityClosed.locus π L,
      ∃ V : S.Opens, x ∈ V ∧ Nonempty
        ((L.pullback (π ⁻¹ᵁ V).ι).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π ⁻¹ᵁ V).toScheme)) :
    IsOpen (ProjectiveTriviality.Construction.ProjectiveTrivialityClosed.locus π L) := by
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  obtain ⟨V, hxV, ⟨e⟩⟩ := hn x hx
  exact ⟨V, (fun y hy => ⟨fiberIso π L V y hy e⟩), V.isOpen, hxV⟩

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenFrame.Construction.OpenFrameFibers
