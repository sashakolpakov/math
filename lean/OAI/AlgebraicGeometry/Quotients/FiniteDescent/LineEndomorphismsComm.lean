import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ReducedSectionsEq

/-! # Line Endomorphisms Comm -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineEndomorphismsComm.Construction.LineEndomorphisms

/-! Endomorphisms of a line bundle commute, independently of any chosen frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem structure_comm {X : Scheme.{u}} (a b : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) : a ≫ b = b ≫ a := by
  apply AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndValue_injective X
  change AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (b * a) = AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (a * b)
  rw [map_mul, map_mul, mul_comm]

/-- Rank-one local freeness makes the entire endomorphism ring commutative. -/
theorem comm {X : Scheme.{u}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (a b : End L.sheaf) : a ≫ b = b ≫ a := by
  apply ReducedSectionsEq.Construction.ReducedSections.moduleMap_eq_of_locally
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyTrivial x
  refine ⟨U, hx, ?_⟩
  let a' : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) :=
    e.inv ≫ (Scheme.Modules.pullback U.ι).map a ≫ e.hom
  let b' : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) :=
    e.inv ≫ (Scheme.Modules.pullback U.ι).map b ≫ e.hom
  have h := structure_comm a' b'
  rw [Functor.map_comp, Functor.map_comp]
  apply (cancel_epi e.inv).mp
  apply (cancel_mono e.hom).mp
  simpa only [a', b', Category.assoc, Iso.hom_inv_id_assoc] using h

/-- An isomorphism between two frames does not change the conjugated scalar endomorphism. -/
theorem frame_independent {X : Scheme.{u}} {M : X.Modules}
    (e f : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (a : End M) :
    e.inv ≫ a ≫ e.hom = f.inv ≫ a ≫ f.hom := by
  let b : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) := e.inv ≫ a ≫ e.hom
  let c : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) := f.inv ≫ e.hom
  have h := structure_comm b c
  apply (cancel_mono (f.inv ≫ e.hom)).mp
  simpa only [b, c, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Category.comp_id] using h

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineEndomorphismsComm.Construction.LineEndomorphisms
