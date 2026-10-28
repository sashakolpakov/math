import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.HopkinsLevitzki

/-! # Artinian Generic Stalk -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ArtinianGenericStalk.Construction

noncomputable section

/-! A nonempty locally Noetherian scheme has an Artinian local ring at
the generic point of each irreducible component, without reducedness. -/

open _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

universe u

theorem exists_artinian_stalk (X : Scheme.{u}) [IsLocallyNoetherian X] [Nonempty X] :
    ∃ x : X, IsArtinianRing (X.presheaf.stalk x) := by
  let z : X := Classical.choice inferInstance
  let C : irreducibleComponents X :=
    ⟨irreducibleComponent z, irreducibleComponent_mem_irreducibleComponents z⟩
  let x : X := irreducibleSetEquivPoints
    ⟨C.val, C.property.1, isClosed_of_mem_irreducibleComponents _ C.property⟩
  have hx : coheight x = 0 := by
    apply IsMax.coheight_eq_zero
    apply (irreducibleSetEquivPoints.isMax_apply).mpr
    intro W hW
    exact C.property.2 W.isIrreducible hW
  have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  exact ⟨x, IsNoetherianRing.isArtinianRing_of_krullDimLE_zero⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ArtinianGenericStalk.Construction
