import OAI.AlgebraicGeometry.Resolution.Blowups.HomogenizedCoefficientChoices
import OAI.AlgebraicGeometry.Resolution.Blowups.CanonicalGlobalCoefficientBound
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalSurface.CenterIndependence

/-! # Homogenization -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

section

/-! Global coefficient bounds and fixed-level surface centers survive replacement by homogenization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData} {n : ℕ}

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.hasBound_homogenize_iff (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (m : ℕ) :
    (∀ i, (A.homogenize.choice i).HasBound m) ↔ ∀ i, (A.choice i).HasBound m := by
  change (∀ i, (A.choice i).homogenize.HasBound m) ↔ ∀ i, (A.choice i).HasBound m
  constructor
  · intro h i
    exact ((A.choice i).homogenize_hasBound_iff m).mp (h i)
  · intro h i
    exact ((A.choice i).homogenize_hasBound_iff m).mpr (h i)

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.coefficientBound_homogenize_eq (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (hc : A.center = ⊤) :
    A.homogenize.coefficientBound (A.homogenize_center.trans hc) = A.coefficientBound hc := by
  apply Nat.le_antisymm
  · apply (A.homogenize.coefficientBound_le_iff (A.homogenize_center.trans hc) _).mpr
    exact (A.hasBound_homogenize_iff _).mpr (A.hasBound_coefficientBound hc)
  · apply (A.coefficientBound_le_iff hc _).mpr
    exact (A.hasBound_homogenize_iff _).mp
      (A.homogenize.hasBound_coefficientBound (A.homogenize_center.trans hc))

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceCenter_homogenize_eq (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (ℓ : ℕ)
    (hb : ∀ i, (A.choice i).HasBound (ℓ + 1))
    (hh : ∀ i, (A.homogenize.choice i).HasBound (ℓ + 1))
    (hdim : ∀ i, ringKrullDim (A.rings i) ≤ 2) (hlevel : (n + 1).factorial ≤ ℓ + 1) :
    A.homogenize.surfaceCenter ℓ hh hdim hlevel = A.surfaceCenter ℓ hb hdim hlevel := by
  apply A.surfaceCenter_unique ℓ hb hdim hlevel
  intro i
  have h := A.homogenize.surfaceCenter_restrict ℓ hh hdim hlevel i
  change (A.homogenize.surfaceCenter ℓ hh hdim hlevel).comap (A.map i) =
    Affine.QuotientKernel.Construction.affineQuotientKernel ((A.choice i).homogenize.toSurfaceTangentChoice ℓ (hh i)).center at h
  rwa [(A.choice i).homogenize_surfaceChoice_center ℓ (hb i) (hh i)] at h

end

/-! Equal homogenizations have the same native coefficient bounds and fixed-level surface centers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J L : X.IdealSheafData} {n : ℕ}

omit [Smooth f] in
theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.hasBound_iff_of_ideal_eq (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n)
    (B : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f L n) (hJL : J = L) (m : ℕ) :
    (∀ i, (A.choice i).HasBound m) ↔ ∀ i, (B.choice i).HasBound m := by
  subst L
  exact A.hasBound_iff_atlas B m

omit [Smooth f] in
theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceCenter_eq_of_ideal_eq (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n)
    (B : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f L n) (hJL : J = L) (ℓ : ℕ)
    (ha : ∀ i, (A.choice i).HasBound (ℓ + 1)) (hb : ∀ i, (B.choice i).HasBound (ℓ + 1))
    (hdA : ∀ i, ringKrullDim (A.rings i) ≤ 2) (hdB : ∀ i, ringKrullDim (B.rings i) ≤ 2)
    (hlevel : (n + 1).factorial ≤ ℓ + 1) :
    A.surfaceCenter ℓ ha hdA hlevel = B.surfaceCenter ℓ hb hdB hlevel := by
  subst L
  exact A.surfaceCenter_eq B ℓ ha hb hdA hdB hlevel

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.hasBound_iff_of_homogenized_eq (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n)
    (B : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f L n)
    (hJL : Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n = Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f L n) (m : ℕ) :
    (∀ i, (A.choice i).HasBound m) ↔ ∀ i, (B.choice i).HasBound m :=
  (A.hasBound_homogenize_iff m).symm.trans
    ((A.homogenize.hasBound_iff_of_ideal_eq B.homogenize hJL m).trans (B.hasBound_homogenize_iff m))

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.hasBound_iff_of_homogenized_interval (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n)
    (B : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f L n) (hJL : J ≤ L)
    (hLH : L ≤ Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n) (m : ℕ) :
    (∀ i, (A.choice i).HasBound m) ↔ ∀ i, (B.choice i).HasBound m :=
  A.hasBound_iff_of_homogenized_eq B (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf_interval_eq f J L n hJL hLH).symm m

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceCenter_eq_of_homogenized_eq (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n)
    (B : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f L n)
    (hJL : Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n = Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f L n) (ℓ : ℕ)
    (ha : ∀ i, (A.choice i).HasBound (ℓ + 1)) (hb : ∀ i, (B.choice i).HasBound (ℓ + 1))
    (hdA : ∀ i, ringKrullDim (A.rings i) ≤ 2) (hdB : ∀ i, ringKrullDim (B.rings i) ≤ 2)
    (hlevel : (n + 1).factorial ≤ ℓ + 1) :
    A.surfaceCenter ℓ ha hdA hlevel = B.surfaceCenter ℓ hb hdB hlevel := by
  have haH := (A.hasBound_homogenize_iff (ℓ + 1)).mpr ha
  have hbH := (B.hasBound_homogenize_iff (ℓ + 1)).mpr hb
  exact (A.surfaceCenter_homogenize_eq ℓ ha haH hdA hlevel).symm.trans
    ((A.homogenize.surfaceCenter_eq_of_ideal_eq B.homogenize hJL ℓ haH hbH hdA hdB hlevel).trans
      (B.surfaceCenter_homogenize_eq ℓ hb hbH hdB hlevel))

end

end OAI.AlgebraicGeometry.Resolution.Blowups
