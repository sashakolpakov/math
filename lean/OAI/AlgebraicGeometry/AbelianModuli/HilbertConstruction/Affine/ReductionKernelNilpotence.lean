import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ReductionKernelSections

/-! # Reduction Kernel Nilpotence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ReductionKernelNilpotence

noncomputable section

/-! Affine sections of the actual reduction kernel lose one power of the
annihilating ideal. All scalar actions are the original section-ring actions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem affineReductionKernel_power_annihilates
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (hf : Function.Surjective f.appTop.hom)
    (M : Y.Modules) [M.IsQuasicoherent] (n : ℕ)
    (h : (RingHom.ker f.appTop.hom) ^ (n + 1) ≤
      Module.annihilator Γ(Y, ⊤) Γ(M, ⊤)) :
    (RingHom.ker f.appTop.hom) ^ n ≤
      Module.annihilator Γ(Y, ⊤) Γ(Closed.ReductionLayer.closedReductionKernel f M, ⊤) := by
  let A := (SectionAdjunction.AffineSectionAdjunction.sections Y).obj M
  let e := (ReductionKernelSections.affineReductionKernelSectionsIso f M).toLinearEquiv
  have hA := NilpotentModuleLayer.quotientModule_unit_kernel_power_annihilates f.appTop.hom hf A n h
  exact hA.trans (e.toLinearMap.annihilator_le_of_injective e.injective)

theorem morphismRestrict_appTop_ker
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    RingHom.ker (f ∣_ U).appTop.hom = RingHom.ker (f.app (U.ι ''ᵁ ⊤)).hom := by
  rw [morphismRestrict_appTop]
  exact RingHom.ker_comp_of_injective _
    (ConcreteCategory.bijective_of_isIso
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op)).injective

theorem module_restrict_top_annihilator
    {X : Scheme.{u}} (U : X.Opens) (M : X.Modules) :
    Module.annihilator Γ(U.toScheme, ⊤) Γ(M.restrict U.ι, ⊤) =
      Module.annihilator Γ(X, U.ι ''ᵁ ⊤) Γ(M, U.ι ''ᵁ ⊤) := by
  ext r
  let r' : Γ(X, U.ι ''ᵁ ⊤) := r
  change (r ∈ Module.annihilator Γ(U.toScheme, ⊤) Γ(M.restrict U.ι, ⊤)) ↔
    (r' ∈ Module.annihilator Γ(X, U.ι ''ᵁ ⊤) Γ(M, U.ι ''ᵁ ⊤))
  rw [Module.mem_annihilator, Module.mem_annihilator]
  have hs (m : Γ(M.restrict U.ι, ⊤)) :
      r • m = (show Γ(X, U.ι ''ᵁ ⊤) from r) •
        (show Γ(M, U.ι ''ᵁ ⊤) from m) := by
    change ((U.ι.appIso ⊤).inv r) • (show Γ(M, U.ι ''ᵁ ⊤) from m) = _
    rw [Scheme.Opens.ι_appIso]
    rfl
  exact forall_congr' fun m => (congrArg (· = 0) (hs m)).to_iff

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ReductionKernelNilpotence
