import OAI.ArithmeticGeometry.Models.SpreadingOut.AffineFiberDensity
import OAI.ArithmeticGeometry.Models.SpreadingOut.FiniteAffineCover

/-! # Scheme Fiber Density -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.SchemeFiberDensity.Construction

noncomputable section

/-! Fiberwise density is preserved by affine coordinates and can be
assembled from a finite affine cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct

universe u

theorem baseChange_dense_open_of_iso
    {B T : Scheme.{u}} {X Y : Over B} (e : X ≅ Y) (g : T ⟶ B)
    (U : X.left.Opens)
    (h : Dense ((pullback.fst Y.hom g) ⁻¹' (e.inv.left ⁻¹' (U : Set X.left)))) :
    Dense ((pullback.fst X.hom g) ⁻¹' (U : Set X.left)) := by
  let k := (Over.pullback g).mapIso e
  have : IsIso k.hom.left := inferInstanceAs (IsIso ((Over.forget T).map k.hom))
  have hk : k.hom.left ≫ (pullback.fst Y.hom g ≫ e.inv.left) =
      pullback.fst X.hom g := by
    erw [← Category.assoc, pullback.lift_fst, Category.assoc, Over.hom_left_inv_left,
      Category.comp_id]
  have hd := h.preimage k.hom.left.isOpenMap
  change Dense ((k.hom.left ≫ (pullback.fst Y.hom g ≫ e.inv.left)) ⁻¹' (U : Set X.left)) at hd
  rwa [hk] at hd

theorem affine_scheme_open_dense_in_fibers_after_shrinking
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (X : Over (Spec (.of R))) [IsAffine X.left] [IsIntegral X.left]
    [IsLocallyNoetherian X.left]
    (U : X.left.Opens) (hU : (U : Set X.left).Nonempty) :
    ∃ r : R, r ≠ 0 ∧
      ∀ (S : Type u) [CommRing S] [Algebra R S], IsUnit (algebraMap R S r) →
        Dense ((pullback.fst X.hom
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))) ⁻¹' (U : Set X.left)) := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)
  let A := Γ(X.left, ⊤)
  let : Algebra R A := φ.hom.toAlgebra
  let e : X ≅ Affine.Construction.affineOver R A := Over.isoMk X.left.isoSpec (by
    change X.left.isoSpec.hom ≫ Spec.map φ = X.hom
    rw [hφ, Iso.hom_inv_id_assoc])
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget (Spec (.of R))).map e.inv))
  have : IsNoetherianRing A :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X.left⟩
  let V : (Spec (.of A)).Opens := e.inv.left ⁻¹ᵁ U
  have hV : (V : Set (Spec (.of A))).Nonempty := by
    obtain ⟨x, hx⟩ := hU
    obtain ⟨y, hy⟩ := e.inv.left.surjective x
    exact ⟨y, by change e.inv.left y ∈ U; rwa [hy]⟩
  obtain ⟨r, hr, hd⟩ := AffineFiberDensity.Construction.affine_open_dense_in_fibers_after_shrinking R A V hV
  refine ⟨r, hr, fun S _ _ hu ↦ ?_⟩
  exact baseChange_dense_open_of_iso e _ U (hd S hu)

theorem dense_of_covering_scheme_maps
    {X : Scheme.{u}} {ι : Type u} (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
    (hcover : ∀ x : X, ∃ i y, f i y = x) (U : Set X)
    (hd : ∀ i, Dense ((f i) ⁻¹' U)) : Dense U := by
  apply dense_iff_inter_open.mpr
  intro V hV hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨i, y, hy⟩ := hcover x
  obtain ⟨z, hzV, hzU⟩ := (hd i).inter_open_nonempty ((f i) ⁻¹' V)
    (hV.preimage (f i).continuous) ⟨y, by change f i y ∈ V; rwa [hy]⟩
  exact ⟨f i z, hzV, hzU⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.SchemeFiberDensity.Construction
