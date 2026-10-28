import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.UnitGluing

/-! # Open Top Unit Gluing -/

namespace OAI.RepresentationTheory.Theta.Geometric.OpenTopUnitGluing

noncomputable section

/-! Gluing native line-bundle frames using global sections of the
open schemes, the coordinates used by affine tensor charts. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem openTopSection_restrict {X : Scheme} {U V : X.Opens} (h : V ≤ U) (r : Γ(X, U)) :
    V.topIso.inv (X.presheaf.map (homOfLE h).op r) =
      (X.homOfLE h).appTop (U.topIso.inv r) := by
  have H : X.presheaf.map (homOfLE h).op ≫ V.topIso.inv =
      U.topIso.inv ≫ (X.homOfLE h).appTop := by
    simp only [Scheme.Opens.topIso_inv, Scheme.homOfLE_appTop, ← Functor.map_comp]
    congr 1
  exact ConcreteCategory.congr_hom H r

def openTopUnitToRegularUnit {X : Scheme} (U : X.Opens) (r : Γ(U.toScheme, ⊤)ˣ) : Γ(X, U)ˣ :=
  Units.map U.topIso.hom.hom.toMonoidHom r

theorem openTopUnit_compatibility {X : Scheme} (U V : X.Opens)
    (r : Γ(U.toScheme, ⊤)ˣ) (s : Γ(V.toScheme, ⊤)ˣ)
    (a b : Γ((U ⊓ V).toScheme, ⊤))
    (h : a * (X.homOfLE (show U ⊓ V ≤ U from inf_le_left)).appTop r =
      (X.homOfLE (show U ⊓ V ≤ V from inf_le_right)).appTop s * b) :
    (U ⊓ V).topIso.hom a *
        (PowerGaugeCover.restrictRegularUnit (show U ⊓ V ≤ U from inf_le_left) (openTopUnitToRegularUnit U r) : Γ(X, U ⊓ V)) =
      (PowerGaugeCover.restrictRegularUnit (show U ⊓ V ≤ V from inf_le_right) (openTopUnitToRegularUnit V s) : Γ(X, U ⊓ V)) * (U ⊓ V).topIso.hom b := by
  apply (ConcreteCategory.bijective_of_isIso (U ⊓ V).topIso.inv).injective
  change (U ⊓ V).topIso.inv
    ((U ⊓ V).topIso.hom a * X.presheaf.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op
      (U.topIso.hom (r : Γ(U.toScheme, ⊤)))) =
    (U ⊓ V).topIso.inv (X.presheaf.map (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op
      (V.topIso.hom (s : Γ(V.toScheme, ⊤))) * (U ⊓ V).topIso.hom b)
  rw [map_mul, map_mul, openTopSection_restrict, openTopSection_restrict,
    Iso.hom_inv_id_apply, Iso.hom_inv_id_apply, Iso.hom_inv_id_apply, Iso.hom_inv_id_apply]
  exact h

theorem exists_iso_of_open_top_units {X : Scheme.{u}} (M N : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (e : ∀ i, M.restrict (U i).ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (U i).toScheme)
    (g : ∀ i, N.restrict (U i).ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (U i).toScheme)
    (r : ∀ i, Γ((U i).toScheme, ⊤)ˣ)
    (a b : ∀ i j, Γ((U i ⊓ U j).toScheme, ⊤))
    (he : ∀ i j,
      (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (show U i ⊓ U j ≤ U i from inf_le_left) (e i)).hom =
        (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (show U i ⊓ U j ≤ U j from inf_le_right) (e j)).hom ≫
          AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (a i j))
    (hg : ∀ i j,
      (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (show U i ⊓ U j ≤ U i from inf_le_left) (g i)).hom =
        (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (show U i ⊓ U j ≤ U j from inf_le_right) (g j)).hom ≫
          AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (b i j))
    (hr : ∀ i j,
      a i j * (X.homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).appTop (r i : Γ((U i).toScheme, ⊤)) =
        (X.homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).appTop (r j : Γ((U j).toScheme, ⊤)) * b i j) :
    Nonempty (M ≅ N) := by
  let r' : ∀ i, Γ(X, U i)ˣ := fun i => openTopUnitToRegularUnit (U i) (r i)
  let a' : ∀ i j, Γ(X, U i ⊓ U j) := fun i j => (U i ⊓ U j).topIso.hom (a i j)
  let b' : ∀ i j, Γ(X, U i ⊓ U j) := fun i j => (U i ⊓ U j).topIso.hom (b i j)
  refine IntrinsicFrame.UnitGluing.exists_iso_of_open_framed_units (X := X) M N (ι := ι) U hU e g r' a' b' ?_ ?_ ?_
  · intro i j
    simpa only [a', Iso.hom_inv_id_apply] using he i j
  · intro i j
    simpa only [b', Iso.hom_inv_id_apply] using hg i j
  · intro i j
    exact openTopUnit_compatibility (U i) (U j) (r i) (r j) (a i j) (b i j) (hr i j)

end

end OAI.RepresentationTheory.Theta.Geometric.OpenTopUnitGluing
