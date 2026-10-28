import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OppositeKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.Tuples
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Etale

/-! # Assembly -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.Assembly.Construction

noncomputable section

/-!
Assemble the actual block subgroup families into a quotient isogeny over
their parameter scheme. The geometric inputs are the complete TorsionQuotient/FiniteDescent
propositions. The local input consists of the torsion projectors and their
orthogonality, rather than any representability or quotient conclusion.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A P : Over S} [GrpObj A] [IsCommMonObj A]

theorem annihilatedBy_of_torsion_projector_separation
    (n : ℕ) (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (p q : A ⟶ A) [IsMonHom p] [IsMonHom q]
    (hkilled : F.KilledBy n) (hsupport : SubgroupFunctor.Construction.SupportedOn F q)
    (hpq : Torsion.Groups.Construction.nativeTorsionMap n q ≫ Torsion.Groups.Construction.nativeTorsionMap n p = 1) : Tuples.Construction.AnnihilatedBy F p := by
  intro X t x hx
  let l := OppositeKernel.Construction.torsionBlockLift n q x (hkilled X t x hx) (hsupport X t x hx)
  have hl : l ≫ OppositeKernel.Construction.torsionBlockInclusion n q = x := OppositeKernel.Construction.torsionBlockLift_inclusion _ _ _ _ _
  rw [← hl, Category.assoc, OppositeKernel.Construction.torsionBlockInclusion_separated n p q hpq, MonObj.comp_one]

/-- The geometric model is derived from the orthogonality of the local
torsion projectors and the actual support of the chosen subgroup families. -/
def separatedTorsionTuple_model
    (n s : ℕ) (F : Fin s → TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : ∀ i, (F i).Model)
    (p : Fin s → (A ⟶ A)) [∀ i, IsMonHom (p i)]
    (hkilled : ∀ i, (F i).KilledBy n) (hsupport : ∀ i, SubgroupFunctor.Construction.SupportedOn (F i) (p i))
    (hsep : ∀ i j, i ≠ j → Torsion.Groups.Construction.nativeTorsionMap n (p j) ≫ Torsion.Groups.Construction.nativeTorsionMap n (p i) = 1) :
    (Tuples.Construction.tupleKernel s F).Model :=
  Tuples.Construction.tupleKernel_model s F R p
    (fun i => (SubgroupFunctor.Construction.supportedOn_iff_model_equation (F i) (R i) (p i)).mp (hsupport i))
    (fun i j hij => (Tuples.Construction.annihilatedBy_iff_model_equation (F j) (R j) (p i)).mp
      (annihilatedBy_of_torsion_projector_separation n (F j) (p i) (p j)
        (hkilled j) (hsupport j) (hsep i j hij)))

/-- Extract TorsionQuotient's finite-etale torsion conclusion in characteristic zero,
using an actual finite module to instantiate its complete proposition. -/
theorem torsion_finite_etale_from_TorsionQuotient
    {K : Type u} [Field K] [CharZero K] (base : S ⟶ Spec (.of K))
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (n : ℕ) (hn : 0 < n) (h_TorsionQuotient : Unit.Construction.TorsionQuotientInput.{u}) :
    IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom ∧ Etale (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have h := h_TorsionQuotient A n hn (Unit.Construction.positive_integer_unit_on_characteristic_zero_base base n hn)
    (ULift.{u} (ZMod n))
  exact ⟨h.1, h.2.1⟩

/-- The separated torsion families produce an actual finite-etale
quotient isogeny, its complementary map, and the prescribed scheme kernel.
This works over the entire parameter scheme and uses TorsionQuotient/FiniteDescent explicitly. -/
theorem quotient_of_separated_torsion_families
    {K : Type u} [Field K] [CharZero K] (base : S ⟶ Spec (.of K))
    (A : Picard.PoincareBundle.Epi.Construction.AbelianScheme S) (P : Over S)
    (n : ℕ) (hn : 0 < n) (s : ℕ)
    (F : Fin s → TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.toOver P) (R : ∀ i, (F i).Model)
    (p : Fin s → (A.toOver ⟶ A.toOver)) [∀ i, IsMonHom (p i)]
    (hkilled : ∀ i, (F i).KilledBy n) (hsupport : ∀ i, SubgroupFunctor.Construction.SupportedOn (F i) (p i))
    (hsep : ∀ i j, i ≠ j → Torsion.Groups.Construction.nativeTorsionMap n (p j) ≫ Torsion.Groups.Construction.nativeTorsionMap n (p i) = 1)
    (h_TorsionQuotient : Unit.Construction.TorsionQuotientInput.{u}) (h_FiniteDescent : IsogenyComplement.Construction.FiniteDescentInput.{u}) :
    let Ftotal := Tuples.Construction.tupleKernel s F
    let Rtotal := separatedTorsionTuple_model n s F R p hkilled hsupport hsep
    ∃ (B : Picard.PoincareBundle.Epi.Construction.AbelianScheme P.left)
      (f : Picard.PoincareBundle.Epi.Construction.AbelianScheme.Isogeny (IsogenyComplement.Construction.baseChangedAbelianScheme A P) B)
      (g : B.toOver ⟶ (IsogenyComplement.Construction.baseChangedAbelianScheme A P).toOver),
      Etale f.hom.left ∧ IsMonHom g ∧
      f.hom ≫ g = (𝟙 (IsogenyComplement.Construction.baseChangedAbelianScheme A P).toOver) ^ n ∧
      g ≫ f.hom = (𝟙 B.toOver) ^ n ∧
      (∀ (T : Over P.left) (a : T ⟶ (IsogenyComplement.Construction.baseChangedAbelianScheme A P).toOver),
        a ≫ f.hom = 1 ↔ ∃! h : T ⟶ (Subgroup.Construction.subgroupGroupScheme Ftotal Rtotal).X,
          h ≫ (Inclusion.Construction.subgroupInclusion Ftotal Rtotal).hom.hom.hom = a) ∧
      Descent.Construction.QuotientUniversalProperty (Inclusion.Construction.subgroupInclusion Ftotal Rtotal).hom.hom.hom f.hom := by
  let Ftotal := Tuples.Construction.tupleKernel s F
  let Rtotal := separatedTorsionTuple_model n s F R p hkilled hsupport hsep
  have htotal : Ftotal.KilledBy n := Tuples.Construction.tupleKernel_killed s F n hkilled
  obtain ⟨B, f, g, hg, hfg, hgf, hker, hUP⟩ :=
    IsogenyComplement.Construction.quotient_isogeny_and_complement_of_FiniteDescent A P Ftotal Rtotal n htotal h_FiniteDescent
  have htor := torsion_finite_etale_from_TorsionQuotient (A := A.toOver) base n hn h_TorsionQuotient
  exact ⟨B, f, g, IsogenyQuotient.Etale.Construction.constructed_quotient_etale A P Ftotal Rtotal n htotal htor.2 B f hker,
    hg, hfg, hgf, hker, hUP⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.Assembly.Construction
