import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.IsotropicPicardRepresentation
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PicardDual

/-! # Isotropic Dual -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.IsotropicDual.Construction

noncomputable section

/-! The canonical isotropic quotient has full dual-abelian data,
including the actual normalized universal line, over a Noetherian base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

attribute [local instance] ParameterKernel.Construction.abelianIsogeny_locallyOfFinitePresentation

variable {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (v : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A)
  (n : ℕ) (hn : 0 < n)
  (hf : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom), x ^ n = 1)
  (hv : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme v.hom), x ^ n = 1)
  (hlag : ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
    let H := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion (A.pullback s).scheme n)
      (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (f.pullback s).hom)
    (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing (A.pullback s) (D.pullback s) (pol.pullback s) n hn).relativeAnnihilator H = H)
  (hc : Nat.Coprime n ((∏ j, δ j) ^ 2))

include pol hf hv hlag hc in
set_option backward.isDefEq.respectTransparency false in
theorem canonicalIsotropicNoetherianQuotientDual_nonempty
    {k : Type} [Field k] [CharZero k] (p : S ⟶ Spec (.of k)) :
    Nonempty (AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) := by
  obtain ⟨Q, q, _r, i, _he, _hr, hi, _hqr, _hrq, _hker, _hquot, hfac, h1, _hmul⟩ :=
    Relative.PicardRepresentation.Construction.relativeCartierQuotientPicardRepresentation_exists D f v
      (Relative.IsotropicPicardRepresentation.Construction.canonicalIsotropicQuotient_geometric_duals D pol f n hn hf hlag hc) p n hn hf hv
  have : IsIso i := hi
  exact ⟨PicardDual.Construction.noetherianPicardQuotientDualData D v Q q i hfac h1⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.IsotropicDual.Construction
