import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UnitPairingTo
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupTransport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Groups
import OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalPairingOrthogonal
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ContainmentMap

/-! # Bundle Self Annihilator -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BundleSelfAnnihilator.Construction

noncomputable section

/-!
The actual PoincareBundle and IsogenyQuotient definitions of self-annihilation agree on every
test scheme. The subgroup in full torsion is the original isogeny kernel,
identified through its literal inclusion into the original source.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

theorem nativeImage_selfAnnihilating_unitPairing_iff
    {S : Scheme.{u}} {H G : Over S} [GrpObj H] [GrpObj G]
    (i : H ⟶ G) [IsMonHom i]
    (b : ∀ T : Over S, (T ⟶ G) →* (T ⟶ G) →* Γ(T.left, ⊤)ˣ)
    (hnatural : ∀ {T U : Over S} (f : U ⟶ T) (x y : T ⟶ G),
      b U (f ≫ x) (f ≫ y) = Units.map f.left.appTop.hom (b T x y)) :
    Picard.PoincareBundle.NaturalPairingOrthogonal.SelfAnnihilating i b ↔
      (UnitPairingTo.Construction.unitPairingToScheme b hnatural).relativeAnnihilator (Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup i) =
        Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup i := by
  have hm (T : Over S) (t : T ⟶ Over.mk (𝟙 S)) (y : T ⟶ G) :
      y ∈ ((UnitPairingTo.Construction.unitPairingToScheme b hnatural).relativeAnnihilator (Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup i)).points T t ↔
        y ∈ Picard.PoincareBundle.NaturalPairingOrthogonal.orthogonal i b T := by
    rw [Annihilator.Construction.SchemeBicharacter.nativeImage_annihilator_membership]
    change (∀ (U : Over S) (f : U ⟶ T) (x : U ⟶ H),
      (UnitPairingTo.Construction.unitPairingToScheme b hnatural).pairValue (x ≫ i) (f ≫ y) = 1) ↔ _
    apply forall_congr'
    intro U
    apply forall_congr'
    intro f
    apply forall_congr'
    intro x
    exact UnitPairingTo.Construction.unitPairingToScheme_value_eq_one_iff b hnatural U (x ≫ i) (f ≫ y)
  constructor
  · intro h
    ext T t y
    exact (hm T t y).trans (h T y)
  · intro h T y
    let t : T ⟶ Over.mk (𝟙 S) := Over.homMk T.hom (Category.comp_id _)
    exact (hm T t y).symm.trans (by
      rw [h]
      rfl)

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] (n : ℕ)
  (hker : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)

instance e45TorsionMap_isMonHom :
    IsMonHom (Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap f n hker) := by
  unfold Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap
  infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem nativeTorsion_kernel_eq_e45_image :
    SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A n) (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f) =
      Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup (Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap f n hker) := by
  ext T t y
  change (y ≫ Torsion.Groups.Construction.nativeTorsionInclusion A n) ≫ f = 1 ↔
    ∃ x : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f,
      x ≫ Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap f n hker = y
  constructor
  · intro hy
    let x := (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv f T).symm ⟨y ≫ Torsion.Groups.Construction.nativeTorsionInclusion A n, hy⟩
    refine ⟨x, ?_⟩
    apply (cancel_mono (Torsion.Groups.Construction.nativeTorsionInclusion A n)).mp
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun a => x ≫ a) (Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap_inclusion f n hker)).trans
        (CategoryTheory.Limits.pullback.lift_fst _ _ _))
  · rintro ⟨x, rfl⟩
    have hi : (x ≫ Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap f n hker) ≫ Torsion.Groups.Construction.nativeTorsionInclusion A n =
        x ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f :=
      (Category.assoc _ _ _).trans
        (congrArg (fun a => x ≫ a) (Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap_inclusion f n hker))
    exact (congrArg (fun a : T ⟶ A => a ≫ f) hi).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun a => x ≫ a) (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion_comp f)).trans (MonObj.comp_one x)))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BundleSelfAnnihilator.Construction
