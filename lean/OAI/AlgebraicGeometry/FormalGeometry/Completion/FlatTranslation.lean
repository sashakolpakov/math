import Mathlib.AlgebraicGeometry.Group.Smooth

/-! # Flat Translation -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FlatTranslation.Construction

noncomputable section

/-! Flatness propagates along actual commuting automorphisms.
The general transport argument is adapted from FlatTranslations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- A commuting pair of automorphisms transports a source open on which
a morphism is flat. -/
theorem flat_preimage_of_commuting_isos
    {X Y : Scheme.{u}} (f : X ⟶ Y) (α : X ≅ X) (β : Y ≅ Y)
    (hcomm : α.hom ≫ f = f ≫ β.hom)
    (U : X.Opens) [Flat (U.ι ≫ f)] :
    Flat ((α.hom ⁻¹ᵁ U).ι ≫ f) := by
  have hflat : Flat ((α.hom ∣_ U) ≫ (U.ι ≫ f)) := inferInstance
  have heq : (α.hom ∣_ U) ≫ (U.ι ≫ f) =
      ((α.hom ⁻¹ᵁ U).ι ≫ f) ≫ β.hom := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hcomm, Category.assoc]
  rw [heq] at hflat
  have : Flat ((((α.hom ⁻¹ᵁ U).ι ≫ f) ≫ β.hom) ≫ β.inv) := inferInstance
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using this

/-- If commuting source/target automorphisms act transitively on closed
source points, flatness on one nonempty source open implies global flatness. -/
theorem flat_of_transitive_automorphisms
    {X Y : Scheme.{u}} [JacobsonSpace X] (f : X ⟶ Y)
    (htrans : ∀ (x y : X), IsClosed {x} → IsClosed {y} →
      ∃ (α : X ≅ X) (β : Y ≅ Y), α.hom x = y ∧ α.hom ≫ f = f ≫ β.hom)
    (U : X.Opens) (hU : (U : Set X).Nonempty) [Flat (U.ι ≫ f)] :
    Flat f := by
  have : IsZariskiLocalAtSource @AlgebraicGeometry.Flat :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Flat)
  let I := {V : X.Opens // Flat (V.ι ≫ f)}
  let V : I → X.Opens := Subtype.val
  have htop : iSup V = ⊤ := by
    by_contra hne
    have hex : ∃ x : X, x ∉ iSup V := by
      by_contra! h
      apply hne
      exact le_antisymm le_top (fun x _ => h x)
    obtain ⟨x₀, hx₀⟩ := hex
    obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints
      (Z := ((iSup V : X.Opens) : Set X)ᶜ) ⟨x₀, hx₀⟩
      (iSup V).isOpen.isClosed_compl.isLocallyClosed
    obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hU U.isOpen.isLocallyClosed
    obtain ⟨α, β, hxy, hcomm⟩ := htrans x y hxc hyc
    let W := α.hom ⁻¹ᵁ U
    have hW : Flat (W.ι ≫ f) := flat_preimage_of_commuting_isos f α β hcomm U
    have hxW : x ∈ W := by
      change α.hom x ∈ U
      rwa [hxy]
    exact hx ((le_iSup V ⟨W, hW⟩) hxW)
  exact IsZariskiLocalAtSource.of_iSup_eq_top
    (P := @AlgebraicGeometry.Flat) (f := f) V htop (fun i => i.prop)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FlatTranslation.Construction
