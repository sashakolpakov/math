import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.PairedKernelType
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELKernelAnnihilator

/-! # PEL Geometric Kernel Type -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELGeometricKernelType

noncomputable section

/-! The two original kernels of a paired PEL quotient over an
algebraically closed characteristic-zero field have the same group
type. Pairing perfection and self-annihilation are constructed from
the actual PEL polarizations and paired isogeny identities. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem pairedPELQuotient_geometric_kernel_type
    {E K k : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [Field k] [IsAlgClosed k] [CharZero k]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {base : Spec (.of k) ⟶ Spec (.of K)}
    {A B : PEL.Objects.PELObject P iota N (Over.mk base)}
    (f : PELQuotients.PairedPELQuotient A B n) (hn : 0 < n)
    (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2)) :
    Nonempty (f.forward.isogeny.kernelAt (Over.mk (𝟙 (Spec (.of k)))) ≃*
      f.reverse.isogeny.kernelAt (Over.mk (𝟙 (Spec (.of k))))) := by
  have : IsLocallyNoetherian (Over.mk base).left :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of k)))
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hunit := TorsionEtaleAt.TorsionEtale.integer_unit_at_stalk (𝟙 (Spec (.of k))) n
  have hA := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme_finite_etale A.polarized.abelian.scheme n
    (AbelianScheme.TorsionQuotient.Etale.TorsionEtale.torsion_finite_etale A.polarized.abelian.scheme n hunit)
  have hB := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme_finite_etale B.polarized.abelian.scheme n
    (AbelianScheme.TorsionQuotient.Etale.TorsionEtale.torsion_finite_etale B.polarized.abelian.scheme n hunit)
  let : IsFinite (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.polarized.abelian.scheme n).hom := hA.1
  let : Etale (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.polarized.abelian.scheme n).hom := hA.2
  let : IsFinite (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B.polarized.abelian.scheme n).hom := hB.1
  let : Etale (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B.polarized.abelian.scheme n).hom := hB.2
  let e := AbelianScheme.IsogenyQuotient.Noetherian.PolarizationAdapter.Construction.noetherianNativePolarizationPairing A.polarized.abelian A.polarized.dual
    A.polarized.polarization n hn
  have he := AbelianScheme.IsogenyQuotient.Noetherian.PolarizationAdapter.Construction.noetherianNativePolarizationPairing_isPerfect A.polarized.abelian A.polarized.dual
    A.polarized.polarization n hn hdegree
  have hs : e.relativeAnnihilator (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n f.forward.isogeny.hom)) =
      AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n f.forward.isogeny.hom) := by
    rw [PELKernelAnnihilator.nativeTorsionMap_kernel_eq]
    exact PELKernelAnnihilator.pairedPELQuotient_forward_kernel_self_annihilating f hn hdegree
  exact Geometric.PairedKernelType.geometric_paired_native_kernel_type f.forward.isogeny.hom f.reverse.isogeny.hom
    n f.forward_reverse f.reverse_forward e he hs

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELGeometricKernelType
