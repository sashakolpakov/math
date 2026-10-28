import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ClosedModuleDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.Annihilator
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.AdjunctionUnit
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms

/-! # Module Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ModuleDescent

noncomputable section

/-! Descent to an actual closed subscheme through the canonical adjunction
unit, under containment of its ideal in the coherent annihilator. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem closedModule_restricted_kernel_annihilates
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (h : f.ker ≤ Coherent.Annihilator.coherentAnnihilator M) (U : Y.affineOpens) :
    RingHom.ker (f ∣_ U.1).appTop.hom ≤
      Module.annihilator Γ(U.1.toScheme, ⊤) Γ(M.restrict U.1.ι, ⊤) := by
  let : IsAffine U.1.toScheme := U.2
  let V : Y.affineOpens := ⟨U.1.ι ''ᵁ ⊤, by rw [U.1.ι_image_top]; exact U.2⟩
  intro r hr
  let r' : Γ(Y, V.1) := r
  have hr0 : (f ∣_ U.1).appTop r = 0 := hr
  rw [morphismRestrict_appTop] at hr0
  have hzero : f.app V.1 r' = 0 := by
    apply (ConcreteCategory.bijective_of_isIso
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U.1 ⊤)).op)).injective
    rw [map_zero]
    exact hr0
  have hker : r' ∈ f.ker.ideal V := by
    rw [Scheme.Hom.ker_apply]
    exact hzero
  have hann : r' ∈ Module.annihilator Γ(Y, V.1) Γ(M, V.1) := h V hker
  apply Module.mem_annihilator.mpr
  intro m
  apply (ConcreteCategory.bijective_of_isIso (M.restrictAppIso U.1.ι ⊤).hom).injective
  rw [map_zero, smul_restrictAppIso_hom_apply]
  rw [Scheme.Opens.ι_appIso]
  exact Module.mem_annihilator.mp hann (show Γ(M, V.1) from m)

theorem closedModule_restrict_unit_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (h : f.ker ≤ Coherent.Annihilator.coherentAnnihilator M) (U : Y.affineOpens) :
    IsIso ((restrictFunctor U.1.ι).map ((pullbackPushforwardAdjunction f).unit.app M)) := by
  let a : M ⟶ (pushforward f).obj ((pullback f).obj M) :=
    (pullbackPushforwardAdjunction f).unit.app M
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
  have hu : IsIso ((pullbackPushforwardAdjunction (f ∣_ U.1)).unit.app (M.restrict U.1.ι)) :=
    Affine.ClosedModuleDescent.affineModule_unit_isIso_of_kernel_annihilates (f ∣_ U.1)
      ((f ∣_ U.1).app_surjective ⊤ (isAffineOpen_top _)) (M.restrict U.1.ι)
      (closedModule_restricted_kernel_annihilates f M h U)
  have := OpenModule.BaseChangeMate.OpenPullbackSquare.openBaseChangeMap_isIso f U.1
  have ha : IsIso ((restrictFunctor U.1.ι).map a ≫
      (OpenModule.BaseChangeMate.OpenPullbackSquare.openBaseChangeMap f U.1).app ((pullback f).obj M)) := by
    rw [OpenPullback.AdjunctionUnit.OpenPullbackSquare.unit_square]
    infer_instance
  exact IsIso.of_isIso_comp_right ((restrictFunctor U.1.ι).map a)
    ((OpenModule.BaseChangeMate.OpenPullbackSquare.openBaseChangeMap f U.1).app ((pullback f).obj M))

theorem closedModule_unit_isIso_of_ideal_annihilates
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (h : f.ker ≤ Coherent.Annihilator.coherentAnnihilator M) :
    IsIso ((pullbackPushforwardAdjunction f).unit.app M) := by
  apply Local.ModuleIsomorphisms.moduleMap_isIso_of_locally
  intro y
  let U : Y.affineOpens :=
    ⟨(Y.affineCover.f (Y.affineCover.idx y)).opensRange, isAffineOpen_opensRange _⟩
  exact ⟨U.1, Y.affineCover.covers y,
    (Power.Nonvanishing.isIso_restrict_map_iff U.1.ι ((pullbackPushforwardAdjunction f).unit.app M)).mp
      (closedModule_restrict_unit_isIso f M h U)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ModuleDescent
