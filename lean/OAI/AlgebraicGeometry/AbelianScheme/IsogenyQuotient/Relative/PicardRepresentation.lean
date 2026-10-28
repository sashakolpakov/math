import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.ImageFromDuals
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ZeroCanonicalPicardImage
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ParameterKernel

/-! # Picard Representation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.PicardRepresentation.Construction

noncomputable section

/-! The actual Cartier quotient of the original dual represents the
whole relative homogeneous Picard sheaf. Both isogeny kernels and the
already constructed geometric quotient duals are retained explicitly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] ParameterKernel.Construction.abelianIsogeny_locallyOfFinitePresentation

universe u
variable {S : Scheme.{u}} {g : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (v : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A)
  (hgeo : ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
    Nonempty (AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData (B.pullback s)))
  {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k))
  (n : ℕ) (hn : 0 < n)
  (hf : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom), x ^ n = 1)
  (hv : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme v.hom), x ^ n = 1)

local notation "C" => OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.FlatKernelCartierRepresentation.Construction.finiteFlatKernelCartierRepresentation v.hom

include f hgeo p hn hf hv in
set_option backward.isDefEq.respectTransparency false in
theorem relativeCartierQuotientPicardRepresentation_exists :
    ∃ (Q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian Q)
      (r : Q.scheme ⟶ (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme)
      (i : uliftYoneda.{u + 1}.obj Q.scheme ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B.scheme).obj),
      Etale q.hom.left ∧ IsMonHom r ∧ IsIso i ∧
      q.hom ≫ r = (𝟙 (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme) ^ n ∧
      r ≫ q.hom = (𝟙 Q.scheme) ^ n ∧
      (∀ (T : Over S) (a : T ⟶ (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme),
        a ≫ q.hom = 1 ↔ ∃! x : T ⟶ (C).dual.X, x ≫ Canonical.DualData.Construction.canonicalCartierPicardInclusion D v.hom C = a) ∧
      Descent.Construction.QuotientUniversalProperty (Canonical.DualData.Construction.canonicalCartierPicardInclusion D v.hom C) q.hom ∧
      uliftYoneda.map q.hom ≫ i = Canonical.PicardPullback.Construction.canonicalPicardPullbackSheafMap D v.hom ∧
      (∀ T : Over S, i.app (op T) (ULift.up (1 : T ⟶ Q.scheme)) = 1) ∧
      (∀ (T : Over S) (x y : T ⟶ Q.scheme),
        i.app (op T) (ULift.up (x * y)) = i.app (op T) (ULift.up x) * i.app (op T) (ULift.up y)) := by
  obtain ⟨Q, q, r, i, he, hr, hi, hqr, hrq, hker, hquot, hfac, h1, hmul⟩ :=
    ZeroCanonicalPicardImage.Construction.charZeroCanonicalPicardImage_exists p D v.hom n hn hv
  have : Mono i := hi
  let F (T : Over S) : (T ⟶ Q.scheme) →* (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B.scheme).obj.obj (op T) := {
    toFun x := i.app (op T) (ULift.up x)
    map_one' := h1 T
    map_mul' := hmul T }
  have hF (T : Over S) (x : T ⟶ Q.scheme) : F T x = i.app (op T) (ULift.up x) := rfl
  exact ⟨Q, q, r, i, he, hr, RelativePicard.ImageFromDuals.Construction.relativePicardImage_isIso_of_geometric_duals D f i F hF hgeo p n hn hf,
    hqr, hrq, hker, hquot, hfac, h1, hmul⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.PicardRepresentation.Construction
