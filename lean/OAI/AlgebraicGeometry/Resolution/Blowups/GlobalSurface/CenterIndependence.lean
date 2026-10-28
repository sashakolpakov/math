import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalSurface.Center
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.CenterRestriction

/-! # Center Independence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Fixed-level native surface centers are independent of the finite affine atlas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceCenter_unique (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (ℓ : ℕ)
    (hb : ∀ i, (A.choice i).HasBound (ℓ + 1))
    (hdim : ∀ i, ringKrullDim (A.rings i) ≤ 2) (hlevel : (n + 1).factorial ≤ ℓ + 1)
    (I : X.IdealSheafData) (hI : ∀ i, I.comap (A.map i) =
      Affine.QuotientKernel.Construction.affineQuotientKernel ((A.choice i).toSurfaceTangentChoice ℓ (hb i)).center) :
    I = A.surfaceCenter ℓ hb hdim hlevel :=
  (GlobalSurface.TangentGluing.Construction.existsUnique_global_surface_tangent_center ℂ f A.rings A.map A.ground A.cover J A.ideals A.ideal_eq
    n ℓ (fun i => (A.choice i).toSurfaceTangentChoice ℓ (hb i)) hdim hlevel).choose_spec.2 I hI

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceCenter_eq (A B : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (ℓ : ℕ)
    (ha : ∀ i, (A.choice i).HasBound (ℓ + 1)) (hb : ∀ i, (B.choice i).HasBound (ℓ + 1))
    (hdA : ∀ i, ringKrullDim (A.rings i) ≤ 2) (hdB : ∀ i, ringKrullDim (B.rings i) ≤ 2)
    (hlevel : (n + 1).factorial ≤ ℓ + 1) :
    A.surfaceCenter ℓ ha hdA hlevel = B.surfaceCenter ℓ hb hdB hlevel := by
  let C := A.append B
  have hc : ∀ i, (C.choice i).HasBound (ℓ + 1) := by
    intro i
    cases i with
    | inl a => exact ha a
    | inr b => exact hb b
  have hdC : ∀ i, ringKrullDim (C.rings i) ≤ 2 := by
    intro i
    cases i with
    | inl a => exact hdA a
    | inr b => exact hdB b
  let I := C.surfaceCenter ℓ hc hdC hlevel
  have hA : I = A.surfaceCenter ℓ ha hdA hlevel :=
    A.surfaceCenter_unique ℓ ha hdA hlevel I (fun i => C.surfaceCenter_restrict ℓ hc hdC hlevel (Sum.inl i))
  have hB : I = B.surfaceCenter ℓ hb hdB hlevel :=
    B.surfaceCenter_unique ℓ hb hdB hlevel I (fun i => C.surfaceCenter_restrict ℓ hc hdC hlevel (Sum.inr i))
  exact hA.symm.trans hB

end

end OAI.AlgebraicGeometry.Resolution.Blowups
