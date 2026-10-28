import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PolarizationEtale
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.GeometricKernelDescent

/-! # Geometric Quotients -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.GeometricQuotients.Construction

noncomputable section

/-! Equal geometric kernels of actual PEL isogenies give equality on all
tests and a genuine quotient isomorphism preserving action and full marking. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k R : Type} [Field k] [IsAlgClosed k] [CommRing R] {g N n m : ℕ}
  {A B C : TateComparison.PEL.PELFamilyData R g N (Spec (.of k))}

theorem pel_kernel_eq_all_tests_of_geometric
    (f : TateComparison.PELIsogenies.PELIsogeny A B n) (e : TateComparison.PELIsogenies.PELIsogeny A C m)
    (δ : Fin g → ℕ) (hA : A.polarizationMap.HasPolarizationType δ)
    (hn : ∀ x : Spec (.of k), IsUnit (n : (Spec (.of k)).presheaf.stalk x))
    (hm : ∀ x : Spec (.of k), IsUnit (m : (Spec (.of k)).presheaf.stalk x))
    (hker : ∀ x : Over.mk (𝟙 (Spec (.of k))) ⟶ A.abelian.scheme,
      x ≫ f.isogeny.hom = 1 ↔ x ≫ e.isogeny.hom = 1)
    (T : Over (Spec (.of k))) (x : T ⟶ A.abelian.scheme) :
    x ≫ f.isogeny.hom = 1 ↔ x ≫ e.isogeny.hom = 1 := by
  have : Etale f.isogeny.hom.left := PolarizationEtale.Construction.pelIsogeny_etale_of_polarization_type f δ hA hn
  have : Etale e.isogeny.hom.left := PolarizationEtale.Construction.pelIsogeny_etale_of_polarization_type e δ hA hm
  have : IsFinite (GroupKernel.Construction.groupKernelScheme f.isogeny.hom).hom :=
    MorphismProperty.of_isPullback (P := @IsFinite)
      (GroupKernel.Construction.groupKernel_isPullback_left f.isogeny.hom) inferInstance
  have : Etale (GroupKernel.Construction.groupKernelScheme f.isogeny.hom).hom :=
    MorphismProperty.of_isPullback (P := @Etale)
      (GroupKernel.Construction.groupKernel_isPullback_left f.isogeny.hom) inferInstance
  have : IsFinite (GroupKernel.Construction.groupKernelScheme e.isogeny.hom).hom :=
    MorphismProperty.of_isPullback (P := @IsFinite)
      (GroupKernel.Construction.groupKernel_isPullback_left e.isogeny.hom) inferInstance
  have : Etale (GroupKernel.Construction.groupKernelScheme e.isogeny.hom).hom :=
    MorphismProperty.of_isPullback (P := @Etale)
      (GroupKernel.Construction.groupKernel_isPullback_left e.isogeny.hom) inferInstance
  exact GeometricKernelDescent.Construction.kernel_eq_all_tests_of_geometric f.isogeny.hom e.isogeny.hom hker T x

/-- This constructs the actual abelian quotient isomorphism and proves
its action and marking equations. Dual and polarization transport remain
separate obligations before invoking the fine PEL moduli classification. -/
theorem exists_pel_quotient_group_iso_of_geometric_kernel
    (f : TateComparison.PELIsogenies.PELIsogeny A B n) (e : TateComparison.PELIsogenies.PELIsogeny A C m)
    (δ : Fin g → ℕ) (hA : A.polarizationMap.HasPolarizationType δ)
    (hn : ∀ x : Spec (.of k), IsUnit (n : (Spec (.of k)).presheaf.stalk x))
    (hm : ∀ x : Spec (.of k), IsUnit (m : (Spec (.of k)).presheaf.stalk x))
    (hker : ∀ x : Over.mk (𝟙 (Spec (.of k))) ⟶ A.abelian.scheme,
      x ≫ f.isogeny.hom = 1 ↔ x ≫ e.isogeny.hom = 1) :
    ∃ j : B.abelian.scheme ≅ C.abelian.scheme,
      IsMonHom j.hom ∧ f.isogeny.hom ≫ j.hom = e.isogeny.hom ∧
      (∀ r : R, TateComparison.End.endSchemeMap B.abelian.scheme (B.action r) ≫ j.hom =
        j.hom ≫ TateComparison.End.endSchemeMap C.abelian.scheme (C.action r)) ∧
      ∀ (T : Over (Spec (.of k)))
        (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))),
        (B.marking.hom.app (.op T) c).val ≫ j.hom = (C.marking.hom.app (.op T) c).val := by
  have hk := pel_kernel_eq_all_tests_of_geometric f e δ hA hn hm hker
  refine ⟨Quotient.Construction.isogenyKernelIso f.isogeny e.isogeny hk,
    Quotient.Construction.isogenyKernelIso_preservesGroup _ _ hk, Quotient.Construction.isogenyKernelIso_fac _ _ hk, ?_, ?_⟩
  · exact Quotient.Construction.isogenyKernelIso_equivariant f e hk
  · exact Quotient.Construction.isogenyKernelIso_marking f e hk

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.GeometricQuotients.Construction
