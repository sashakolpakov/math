import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.BasisIsomorphisms

/-! # Open Map Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.OpenMapGluing

noncomputable section

/-! Glue module maps on an open cover using their compatible ambient section values. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u v

variable {X : Scheme.{u}} {M N : X.Modules}

def moduleMapOnOpen (U : X.Opens) (φ : M.restrict U.ι ⟶ N.restrict U.ι)
    (V : X.Opens) (h : V ≤ U) : Γ(M, V) →ₗ[Γ(X, V)] Γ(N, V) :=
  OpenModule.MapValues.openModuleMapValue U.ι φ V (by simpa only [U.opensRange_ι] using h)

variable {ι : Type v} (U : ι → X.Opens)

abbrev SubordinateOpenIndex := {V : X.Opens // ∃ i, V ≤ U i}

def subordinateOpenBasis : SubordinateOpenIndex U → X.Opens := Subtype.val

theorem subordinateOpenBasis_isBasis (hU : ∀ x : X, ∃ i, x ∈ U i) :
    Opens.IsBasis (Set.range (subordinateOpenBasis U)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro V x hx
  obtain ⟨i, hxi⟩ := hU x
  exact ⟨V ⊓ U i, ⟨⟨V ⊓ U i, i, inf_le_right⟩, rfl⟩, ⟨hx, hxi⟩, inf_le_left⟩

structure OpenCoverModuleMaps (M N : X.Modules) where
  localMap : ∀ i, M.restrict (U i).ι ⟶ N.restrict (U i).ι
  agree : ∀ i j (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j),
    moduleMapOnOpen (U i) (localMap i) V hi = moduleMapOnOpen (U j) (localMap j) V hj

namespace OpenCoverModuleMaps

variable {U} (D : OpenCoverModuleMaps U M N)

def basisMap : MapBasisExtension.ModuleBasisMap (subordinateOpenBasis U) M N where
  app V := moduleMapOnOpen (U (Classical.choose V.property))
    (D.localMap (Classical.choose V.property)) V.val (Classical.choose_spec V.property)
  naturality V W h s := by
    have hv := Classical.choose_spec V.property
    have hw := Classical.choose_spec W.property
    change moduleMapOnOpen _ _ V.val hv (M.presheaf.map (homOfLE h).op s) = _
    rw [D.agree (Classical.choose V.property) (Classical.choose W.property) V.val hv (h.trans hw)]
    exact OpenModule.MapValues.openModuleMapValue_natural _ _ h _ _ s

variable (hU : ∀ x : X, ∃ i, x ∈ U i)

def glue : M ⟶ N := D.basisMap.extend (subordinateOpenBasis_isBasis U hU)

theorem glue_app (i : ι) (V : X.Opens) (hi : V ≤ U i) (s : Γ(M, V)) :
    (D.glue hU).app V s = moduleMapOnOpen (U i) (D.localMap i) V hi s := by
  let W : SubordinateOpenIndex U := ⟨V, i, hi⟩
  have h := D.basisMap.extend_app (subordinateOpenBasis_isBasis U hU) W s
  exact h.trans (LinearMap.congr_fun
    (D.agree (Classical.choose W.property) i V (Classical.choose_spec W.property) hi) s)

theorem glue_restrict (i : ι) :
    (Scheme.Modules.restrictFunctor (U i).ι).map (D.glue hU) = D.localMap i := by
  apply OpenModule.MapRecovery.openModuleMapValue_injective (U i).ι
  intro V hV
  rw [OpenModule.MapValues.openModuleMapValue_from_global]
  apply LinearMap.ext
  intro s
  have hi : V ≤ U i := by simpa only [(U i).opensRange_ι] using hV
  exact D.glue_app hU i V hi s

theorem glue_unique (φ : M ⟶ N)
    (hφ : ∀ i, (Scheme.Modules.restrictFunctor (U i).ι).map φ = D.localMap i) : φ = D.glue hU := by
  apply BasisIsomorphisms.moduleMap_eq_of_basis (subordinateOpenBasis U) (subordinateOpenBasis_isBasis U hU)
  intro V
  apply ConcreteCategory.hom_ext
  intro s
  obtain ⟨i, hi⟩ := V.property
  have hv := congrArg (fun ψ => moduleMapOnOpen (U i) ψ V.val hi s) (hφ i)
  have hglobal : moduleMapOnOpen (U i) ((Scheme.Modules.restrictFunctor (U i).ι).map φ) V.val hi s =
      φ.app V.val s := LinearMap.congr_fun (OpenModule.MapValues.openModuleMapValue_from_global (U i).ι φ V.val _) s
  exact hglobal.symm.trans (hv.trans (D.glue_app hU i V.val hi s).symm)

end OpenCoverModuleMaps

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.OpenMapGluing
