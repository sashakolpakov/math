import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.PicardRepresentation
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.DualExistence

/-! # Isotropic Picard Representation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.IsotropicPicardRepresentation.Construction

noncomputable section

/-! Full relative Picard representability for the canonical isotropic
quotient. The geometric duals are constructed from the original
polarization and isotropy, rather than supplied as extra data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

attribute [local instance] ParameterKernel.Construction.abelianIsogeny_locallyOfFinitePresentation

variable {S : Scheme.{0}} {g : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
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

include hf hlag hc in
theorem canonicalIsotropicQuotient_geometric_duals
    (K : Type) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S) :
    Nonempty (AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData (B.pullback s)) :=
  Canonical.DualExistence.Construction.geometricCanonicalQuotientDual_nonempty D pol K s n hn (f.pullback s)
    (ParameterKernel.Construction.isogeny_baseChange_kernelPoint_pow f n hf s) (hlag K s) hc

local notation "C" => OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.FlatKernelCartierRepresentation.Construction.finiteFlatKernelCartierRepresentation v.hom

include pol hf hv hlag hc in
set_option backward.isDefEq.respectTransparency false in
theorem canonicalIsotropicRelativePicardRepresentation_exists
    {k : Type} [Field k] [CharZero k] (p : S ⟶ Spec (.of k)) :
    ∃ (Q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian Q)
      (i : uliftYoneda.{1}.obj Q.scheme ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B.scheme).obj),
      IsIso i ∧ Etale q.hom.left ∧
      uliftYoneda.map q.hom ≫ i = Canonical.PicardPullback.Construction.canonicalPicardPullbackSheafMap D v.hom ∧
      Descent.Construction.QuotientUniversalProperty (Canonical.DualData.Construction.canonicalCartierPicardInclusion D v.hom C) q.hom ∧
      (∀ (T : Over S) (a : T ⟶ (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme),
        a ≫ q.hom = 1 ↔ ∃! x : T ⟶ (C).dual.X, x ≫ Canonical.DualData.Construction.canonicalCartierPicardInclusion D v.hom C = a) := by
  obtain ⟨Q, q, r, i, he, _, hi, _, _, hker, hquot, hfac, _, _⟩ :=
    PicardRepresentation.Construction.relativeCartierQuotientPicardRepresentation_exists D f v
      (canonicalIsotropicQuotient_geometric_duals D pol f n hn hf hlag hc) p n hn hf hv
  exact ⟨Q, q, i, hi, he, hfac, hquot, hker⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.IsotropicPicardRepresentation.Construction
