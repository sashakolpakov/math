import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ReducedFiber
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.GroupKernel
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ScalarIsogeny

/-! # Polarization Etale -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PolarizationEtale.Construction

noncomputable section

/-! The degree and geometric kernel type of a polarization prove its
etaleness on an algebraically closed fiber. The polarization equation then
proves etaleness of every PEL isogeny with an invertible multiplier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {g N n : ℕ}

theorem polarization_kernel_etale
    {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (p : A.Isogeny B)
    (δ : Fin g → ℕ) (hp : p.HasPolarizationType δ) :
    Etale (GroupKernel.Construction.groupKernelScheme p.hom).hom := by
  have : IsFinite (GroupKernel.Construction.groupKernelScheme p.hom).hom :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GroupKernel.Construction.groupKernel_isPullback_left p.hom) inferInstance
  have : Flat (GroupKernel.Construction.groupKernelScheme p.hom).hom :=
    MorphismProperty.of_isPullback (P := @Flat) (GroupKernel.Construction.groupKernel_isPullback_left p.hom) inferInstance
  have hcount : Nat.card (Over.mk (𝟙 (Spec (.of k))) ⟶ GroupKernel.Construction.groupKernelScheme p.hom) =
      (∏ i, δ i) ^ 2 := by
    calc
      _ = Nat.card (p.kernelAt (Over.mk (𝟙 (Spec (.of k))))) :=
        Nat.card_congr (GroupKernel.Construction.groupKernelPointsEquiv p.hom _)
      _ = _ := by
        rw [Nat.card_congr (hp.geometricKernel k (𝟙 _)).some.toEquiv]
        change Nat.card ((∀ i, ZMod (δ i)) × (∀ i, ZMod (δ i))) = _
        rw [Nat.card_prod, Nat.card_pi]
        simp only [Nat.card_zmod, ← pow_two]
  apply ReducedFiber.Construction.finite_field_scheme_etale_of_point_count k
  rw [hcount, Scheme.Hom.finrank_of_isPullback _ _ _ _ (GroupKernel.Construction.groupKernel_isPullback_left p.hom)]
  exact (hp.degree _).symm

theorem polarization_etale
    {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (p : A.Isogeny B)
    (δ : Fin g → ℕ) (hp : p.HasPolarizationType δ) : Etale p.hom.left := by
  have : IsFinite (GroupKernel.Construction.groupKernelScheme p.hom).hom :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GroupKernel.Construction.groupKernel_isPullback_left p.hom) inferInstance
  have : Etale (GroupKernel.Construction.groupKernelScheme p.hom).hom := polarization_kernel_etale p δ hp
  have : FormallyUnramified p.hom.left := GroupKernel.Construction.groupHom_unramified_of_etale_kernel p.hom
  have : IsLocallyNoetherian B.scheme.left := LocallyOfFiniteType.isLocallyNoetherian B.scheme.hom
  have : LocallyOfFinitePresentation p.hom.left := inferInstance
  exact Etale.of_formallyUnramified_of_flat _

variable {R : Type} [CommRing R]

/-- The source polarization and the actual PEL equation prove etaleness;
no separability or reduced-kernel assumption is imposed on the isogeny. -/
theorem pelIsogeny_etale_of_polarization_type
    {A B : TateComparison.PEL.PELFamilyData R g N (Spec (.of k))} (f : TateComparison.PELIsogenies.PELIsogeny A B n)
    (δ : Fin g → ℕ) (hA : A.polarizationMap.HasPolarizationType δ)
    (hn : ∀ x : Spec (.of k), IsUnit (n : (Spec (.of k)).presheaf.stalk x)) :
    Etale f.isogeny.hom.left := by
  have : Etale A.polarizationMap.hom.left := polarization_etale A.polarizationMap δ hA
  have : Etale ((𝟙 A.dual.abelian.scheme) ^ n).left :=
    (ScalarIsogeny.Construction.abelian_multiplier_finite_etale_surjective A.dual.abelian n hn).2.1
  have hpower : (A.polarizationMap.hom ^ n).left =
      A.polarizationMap.hom.left ≫ ((𝟙 A.dual.abelian.scheme) ^ n).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have : Etale (A.polarizationMap.hom ^ n).left := by rw [hpower]; infer_instance
  have hpol : f.isogeny.hom.left ≫ (B.polarizationMap.hom.left ≫ f.dualHom.left) =
      (A.polarizationMap.hom ^ n).left := congrArg Over.Hom.left f.polarization
  have : FormallyUnramified (f.isogeny.hom.left ≫
      (B.polarizationMap.hom.left ≫ f.dualHom.left)) := by rw [hpol]; infer_instance
  have : FormallyUnramified f.isogeny.hom.left := FormallyUnramified.of_comp
    f.isogeny.hom.left (B.polarizationMap.hom.left ≫ f.dualHom.left)
  have : IsLocallyNoetherian B.abelian.scheme.left :=
    LocallyOfFiniteType.isLocallyNoetherian B.abelian.scheme.hom
  have : LocallyOfFinitePresentation f.isogeny.hom.left := inferInstance
  exact Etale.of_formallyUnramified_of_flat _

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PolarizationEtale.Construction
