import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CharZeroPicardImage
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.FlatKernelCartierRepresentation

/-! # Zero Canonical Picard Image -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ZeroCanonicalPicardImage.Construction

noncomputable section

/-! Construct the actual Cartier representative and relative Picard
image from the original isogeny data over a characteristic-zero base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k))
  {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {X : Over S} [GrpObj X] [IsCommMonObj X]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  (f : X ⟶ A.scheme) [IsMonHom f] [IsFinite f.left] [Flat f.left] [Surjective f.left]
  [LocallyOfFinitePresentation f.left]

local notation "C" => OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.FlatKernelCartierRepresentation.Construction.finiteFlatKernelCartierRepresentation f

include p in
theorem charZeroCanonicalPicardImage_exists (n : ℕ) (hn : 0 < n)
    (hk : ∀ (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1) :
    ∃ (Q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian Q)
      (r : Q.scheme ⟶ (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme)
      (i : uliftYoneda.{u + 1}.obj Q.scheme ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf X).obj),
      Etale q.hom.left ∧ IsMonHom r ∧ Mono i ∧
      q.hom ≫ r = (𝟙 (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme) ^ n ∧
      r ≫ q.hom = (𝟙 Q.scheme) ^ n ∧
      (∀ (T : Over S) (a : T ⟶ (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme),
        a ≫ q.hom = 1 ↔ ∃! x : T ⟶ (C).dual.X, x ≫ Canonical.DualData.Construction.canonicalCartierPicardInclusion D f C = a) ∧
      Descent.Construction.QuotientUniversalProperty (Canonical.DualData.Construction.canonicalCartierPicardInclusion D f C) q.hom ∧
      uliftYoneda.map q.hom ≫ i = Canonical.PicardPullback.Construction.canonicalPicardPullbackSheafMap D f ∧
      (∀ T : Over S, i.app (op T) (ULift.up (1 : T ⟶ Q.scheme)) = 1) ∧
      (∀ (T : Over S) (x y : T ⟶ Q.scheme),
        i.app (op T) (ULift.up (x * y)) = i.app (op T) (ULift.up x) * i.app (op T) (ULift.up y)) :=
  CharZeroPicardImage.Construction.charZeroCartierPicardImage_exists p D f C n hn hk

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ZeroCanonicalPicardImage.Construction
