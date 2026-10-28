import OAI.RepresentationTheory.Theta.Geometric.PELMultiplicationDual
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.MultiplicationPELIsogeny
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplementaryIsogeny
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicPoincare

/-! # PEL Complement Dual -/

namespace OAI.RepresentationTheory.Theta.Geometric.PELComplementDual

noncomputable section

/-! Canonical Picard duality for the actual complementary isogeny,
including its exact composition with the original PEL dual map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicPoincare.Construction.IntrinsicPicardPullback

universe u
variable {k : Type u} [Field k] {S : Scheme.{u}} {r t : ℕ}
    {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme r S} {B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme t S}

theorem nativeDualMap_congr (DA : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
    (f g : A.scheme ⟶ B.scheme) [IsMonHom f] [IsMonHom g] (h : f = g) :
    AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB = AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap g DA DB := by
  subst g
  rfl

theorem nativeDualMap_group
    {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme r (Spec (.of k))} {B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme t (Spec (.of k))}
    (DA : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
    (f : A.scheme ⟶ B.scheme) [IsMonHom f] : IsMonHom (AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB) := by
  apply AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.GroupRigidity.Construction.pointed_isMonHom_over_field DB.abelian.scheme DA.abelian.scheme
  simpa only [Hom.one_def, CartesianMonoidalCategory.toUnit_unit, Category.id_comp] using
    AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap_one f DA DB (𝟙_ (Over (Spec (.of k))))

variable {R k : Type} [CommRing R] [Field k] [CharZero k] [IsAlgClosed k]
    {g N q m : ℕ} [Fact q.Prime]
    {P Q : AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData R g N (Spec (.of k))}
    (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny P Q (q ^ m))
    (δ : Fin g → ℕ) (hP : P.polarizationMap.HasPolarizationType δ)
    (hQ : Q.polarizationMap.HasPolarizationType δ) (hq : Nat.Coprime q (∏ i, δ i))

theorem complementary_dual_factor :
    e.dualHom ≫ AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (e.multiplierComplement δ hP hQ hq).hom Q.dual P.dual =
      (𝟙 Q.dual.abelian.scheme) ^ (q ^ m) := by
  have hd : e.dualHom = AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.isogeny.hom P.dual Q.dual :=
    AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardAdjoints.Construction.NativePicardPullback.dualMap_eq_of_poincare e.isogeny.hom P.dual Q.dual e.dualHom e.poincare.symm
  rw [hd, ← AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap_comp (e.multiplierComplement δ hP hQ hq).hom Q.dual P.dual Q.dual e.isogeny.hom]
  exact (nativeDualMap_congr Q.dual Q.dual _ _
    (e.multiplierComplementHom_comp δ hP hQ hq)).trans (by
      exact (AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardAdjoints.Construction.NativePicardPullback.dualMap_eq_of_poincare ((𝟙 Q.abelian.scheme) ^ (q ^ m)) Q.dual Q.dual
        ((𝟙 Q.dual.abelian.scheme) ^ (q ^ m)) (AlgebraicGeometry.AbelianScheme.TateComparison.MultiplicationPELIsogeny.multiplication_poincare Q (q ^ m)).symm).symm)

end

end OAI.RepresentationTheory.Theta.Geometric.PELComplementDual
