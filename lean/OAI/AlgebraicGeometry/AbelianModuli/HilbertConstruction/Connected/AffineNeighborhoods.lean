import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.ConnectedComponents
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Affine Neighborhoods -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.AffineNeighborhoods

noncomputable section

/-! Every point of a locally Noetherian scheme has a connected Noetherian affine open neighborhood, obtained from a closed connected component of an affine chart. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem noetherianConnectedComponentOpen_affine
    (X : Scheme.{u}) [IsNoetherian X] [IsAffine X] (x : X) :
    IsAffine (Noetherian.ConnectedComponents.noetherianConnectedComponentOpen X x).toScheme := by
  let U := Noetherian.ConnectedComponents.noetherianConnectedComponentOpen X x
  have hU : IsClosed (U : Set X) := isClosed_connectedComponent
  have : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι
    (U.range_ι.symm ▸ hU)
  exact isAffine_of_isAffineHom U.ι

theorem exists_connected_affine_openNeighborhood
    (S : Scheme.{u}) [IsLocallyNoetherian S] (x : S) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ S), IsOpenImmersion f ∧ IsAffine Y ∧ IsNoetherian Y ∧
      ConnectedSpace Y ∧ x ∈ Set.range f := by
  obtain ⟨_, ⟨U : S.Opens, hU, rfl⟩, hx, _⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : IsAffine U.toScheme := hU
  have : IsNoetherianRing Γ(U.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have : IsNoetherian U.toScheme :=
    (isNoetherian_iff_of_finite_iSup_eq_top
      (S := fun _ : Unit => (⟨⊤, isAffineOpen_top U.toScheme⟩ : U.toScheme.affineOpens)) (by simp)).mpr
        (fun _ => inferInstance)
  let y : U.toScheme := ⟨x, hx⟩
  let V := Noetherian.ConnectedComponents.noetherianConnectedComponentOpen U.toScheme y
  have : IsAffine V.toScheme := noetherianConnectedComponentOpen_affine U.toScheme y
  have hVloc : IsLocallyNoetherian V.toScheme :=
    @isLocallyNoetherian_of_isOpenImmersion V.toScheme U.toScheme V.ι inferInstance inferInstance
  have : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := hVloc, toCompactSpace := inferInstance }
  have : ConnectedSpace V.toScheme := Noetherian.ConnectedComponents.noetherianConnectedComponentOpen_connected U.toScheme y
  refine ⟨V.toScheme, V.ι ≫ U.ι, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨⟨y, mem_connectedComponent⟩, rfl⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.AffineNeighborhoods
