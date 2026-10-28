import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SchemeIdealModule

/-! # Frames -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.Frames.Cycles.LineBundleConstruction

noncomputable section

/-!
# LineBundleCycles: frames on sections of actual open subschemes

These linear equivalences come from the line bundle's actual local sheaf
isomorphisms. They will allow transition functions to be compared on different
ambient opens without introducing a cohomological compatibility hypothesis.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme.{0}} (M : X.Modules) (U : X.Opens)

def structureModuleSectionToRing (W : U.toScheme.Opens) :
    Γ(DivisorClass.Chern.Line.Bundles.Construction.structureModule U.toScheme, W) → Γ(X, U.ι ''ᵁ W) := fun r => r

theorem structureModuleSectionToRing_smul (W : U.toScheme.Opens)
    (r : Γ(X, U.ι ''ᵁ W)) (s : Γ(DivisorClass.Chern.Line.Bundles.Construction.structureModule U.toScheme, W)) :
    structureModuleSectionToRing U W (((DivisorClass.Chern.Line.Bundles.Construction.structureModule U.toScheme).smul (U := W) r).hom s) =
      r * structureModuleSectionToRing U W s := rfl

/-- Restriction along an actual open-subscheme inclusion preserves the section scalar action. -/
theorem openRestriction_smul (W : U.toScheme.Opens)
    (r : Γ(X, U.ι ''ᵁ W)) (m : Γ(M, U.ι ''ᵁ W)) :
    (M.smul (U := U.ι ''ᵁ W) r).hom m =
      ((M.restrict U.ι).smul (U := W) (r : Γ(U.toScheme, W))).hom m := by
  have h := ConcreteCategory.congr_hom
    (Scheme.Modules.smul_restrictAppIso_inv U.ι M W r) m
  rw [Scheme.Opens.ι_appIso] at h
  exact h

/-- A genuine sheaf trivialization gives a linear frame on every subopen's sections. -/
def frameOnImage (e : M.restrict U.ι ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule U.toScheme)
    (W : U.toScheme.Opens) :
    Γ(M, U.ι ''ᵁ W) ≃ₗ[Γ(X, U.ι ''ᵁ W)] Γ(X, U.ι ''ᵁ W) where
  toFun m := e.hom.app W m
  invFun r := e.inv.app W r
  left_inv m := by
    have h := congrArg (fun f : M.restrict U.ι ⟶ M.restrict U.ι => f.app W) e.hom_inv_id
    exact ConcreteCategory.congr_hom h m
  right_inv r := by
    have h := congrArg (fun f : DivisorClass.Chern.Line.Bundles.Construction.structureModule U.toScheme ⟶ DivisorClass.Chern.Line.Bundles.Construction.structureModule U.toScheme =>
      f.app W) e.inv_hom_id
    exact ConcreteCategory.congr_hom h r
  map_add' m n := (e.hom.app W).hom.map_add m n
  map_smul' r m := by
    change structureModuleSectionToRing U W (e.hom.app W (r • m)) =
      r * structureModuleSectionToRing U W (e.hom.app W m)
    exact (congrArg (structureModuleSectionToRing U W)
      ((congrArg (e.hom.app W) (openRestriction_smul M U W r m)).trans
        (e.hom.app_smul r m))).trans (structureModuleSectionToRing_smul U W r (e.hom.app W m))

/-- The frame coordinates commute with the actual restrictions of module sections. -/
theorem frameOnImage_naturality
    (e : M.restrict U.ι ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule U.toScheme)
    {V W : U.toScheme.Opens} (h : V ≤ W) (m : Γ(M, U.ι ''ᵁ W)) :
    frameOnImage M U e V
        (M.presheaf.map (homOfLE (U.ι.image_mono h)).op m) =
      X.presheaf.map (homOfLE (U.ι.image_mono h)).op (frameOnImage M U e W m) := by
  have hn := ConcreteCategory.congr_hom
    (e.hom.mapPresheaf.naturality (homOfLE h).op) m
  exact hn

/-- Transport frame coordinates along equality of open subsets. -/
def transportFrame {V W : X.Opens} (h : V = W)
    (e : Γ(M, V) ≃ₗ[Γ(X, V)] Γ(X, V)) :
    Γ(M, W) ≃ₗ[Γ(X, W)] Γ(X, W) :=
  h ▸ e

/-- Naturality survives the canonical transports along equal open sets. -/
theorem transportFrame_naturality {A B A' B' : X.Opens}
    (hA : A = A') (hB : B = B') (h : B ≤ A) (h' : B' ≤ A')
    (eA : Γ(M, A) ≃ₗ[Γ(X, A)] Γ(X, A))
    (eB : Γ(M, B) ≃ₗ[Γ(X, B)] Γ(X, B))
    (hn : ∀ m, eB (M.presheaf.map (homOfLE h).op m) =
      X.presheaf.map (homOfLE h).op (eA m)) (m : Γ(M, A')) :
    transportFrame M hB eB (M.presheaf.map (homOfLE h').op m) =
      X.presheaf.map (homOfLE h').op (transportFrame M hA eA m) := by
  subst A'
  subst B'
  exact hn m

theorem image_preimage_subopen {V : X.Opens} (h : V ≤ U) :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
  simpa only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    using inf_eq_right.mpr h

/-- A local sheaf trivialization gives a frame on every smaller ambient open. -/
def frameOnOpen (e : M.restrict U.ι ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule U.toScheme)
    (V : X.Opens) (h : V ≤ U) : Γ(M, V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
  transportFrame M (image_preimage_subopen U h) (frameOnImage M U e (U.ι ⁻¹ᵁ V))

/-- Ambient-open frame coordinates commute with actual module restrictions. -/
theorem frameOnOpen_naturality
    (e : M.restrict U.ι ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule U.toScheme)
    {V W : X.Opens} (hVW : V ≤ W) (hWU : W ≤ U)
    (m : Γ(M, W)) :
    frameOnOpen M U e V (hVW.trans hWU) (M.presheaf.map (homOfLE hVW).op m) =
      X.presheaf.map (homOfLE hVW).op (frameOnOpen M U e W hWU m) := by
  exact transportFrame_naturality M
    (image_preimage_subopen U hWU) (image_preimage_subopen U (hVW.trans hWU))
    (U.ι.image_mono (show U.ι ⁻¹ᵁ V ≤ U.ι ⁻¹ᵁ W from fun _ hx => hVW hx)) hVW
    (frameOnImage M U e (U.ι ⁻¹ᵁ W)) (frameOnImage M U e (U.ι ⁻¹ᵁ V))
    (fun m => frameOnImage_naturality M U e
      (show U.ι ⁻¹ᵁ V ≤ U.ι ⁻¹ᵁ W from fun _ hx => hVW hx) m) m

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.Frames.Cycles.LineBundleConstruction
