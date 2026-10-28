import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.IsogenyPolarizationSymmetry
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.IsogenyLevelSymmetry
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionEtaleAt
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyFactorizationIs
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.PELBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.DualComplement
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ScalarComplement

/-! # PEL Quotients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELQuotients

noncomputable section

/-! Paired actual PEL quotients admit a literal swap involution.
The reverse quotient's polarization, action, and ordered marking are
proved from the forward quotient and the scalar complement identities. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K]
    {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T : Over (Spec (.of K))} {A B : PEL.Objects.PELObject P iota N T} {n : ℕ}

structure PairedPELQuotient (A B : PEL.Objects.PELObject P iota N T) (n : ℕ) where
  forward : AbelianScheme.IsogenyQuotient.Intrinsic.PELBaseChange.Construction.NativePELQuotient A B n
  reverse : AbelianScheme.IsogenyQuotient.Intrinsic.PELBaseChange.Construction.NativePELQuotient B A n
  forward_reverse : forward.isogeny.hom ≫ reverse.isogeny.hom =
    (𝟙 A.polarized.abelian.scheme) ^ n
  reverse_forward : reverse.isogeny.hom ≫ forward.isogeny.hom =
    (𝟙 B.polarized.abelian.scheme) ^ n

def PairedPELQuotient.swap (f : PairedPELQuotient A B n) : PairedPELQuotient B A n where
  forward := f.reverse
  reverse := f.forward
  forward_reverse := f.reverse_forward
  reverse_forward := f.forward_reverse

theorem PairedPELQuotient.swap_swap (f : PairedPELQuotient A B n) : f.swap.swap = f := rfl

variable [CharZero K] [IsLocallyNoetherian T.left]

def scalarComplementPELQuotient (f : AbelianScheme.IsogenyQuotient.Intrinsic.PELBaseChange.Construction.NativePELQuotient A B n)
    (v : HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B.polarized.abelian A.polarized.abelian)
    (hn : 0 < n) (hmod : Nat.ModEq N n 1)
    (hfv : f.isogeny.hom ≫ v.hom = (𝟙 A.polarized.abelian.scheme) ^ n)
    (hvf : v.hom ≫ f.isogeny.hom = (𝟙 B.polarized.abelian.scheme) ^ n) :
    AbelianScheme.IsogenyQuotient.Intrinsic.PELBaseChange.Construction.NativePELQuotient B A n := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : Etale f.isogeny.hom.left := f.etale
  have hmult : Etale (((𝟙 B.polarized.abelian.scheme) ^ n).left) :=
    AbelianScheme.TorsionQuotient.Etale.TorsionEtale.power_etale B.polarized.abelian.scheme n
      (TorsionEtaleAt.TorsionEtale.integer_unit_at_stalk T.hom n)
  have : Etale (v.hom.left ≫ f.isogeny.hom.left) := by
    change Etale (v.hom ≫ f.isogeny.hom).left
    rw [hvf]
    exact hmult
  have hve : Etale v.hom.left := Etale.of_comp v.hom.left f.isogeny.hom.left
  let : EffectiveEpi f.isogeny.hom :=
    PELModuli.IntegralModel.IsogenyFactorizationIs.IsogenyFactorization.effectiveEpi_over_of_fpqc f.isogeny.hom
  let : EffectiveEpi v.hom := PELModuli.IntegralModel.IsogenyFactorizationIs.IsogenyFactorization.effectiveEpi_over_of_fpqc v.hom
  have hdual := (AbelianScheme.IsogenyQuotient.Noetherian.DualComplement.Construction.noetherian_nativeDualMap_complements A.polarized.dual B.polarized.dual
    f.isogeny v n hfv hvf).1
  refine {
    isogeny := v
    etale := hve
    polarization := ?_
    action := ?_
    marking := IsogenyLevelSymmetry.paired_quotient_level_relation_symmetric A.polarized.abelian B.polarized.abelian
      A.polarized.level B.polarized.level f.isogeny.hom v.hom hfv hmod f.marking }
  · exact IsogenyPolarizationSymmetry.paired_quotient_polarization_relation_symmetric f.isogeny.hom v.hom
      (AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.isogeny.hom A.polarized.dual B.polarized.dual)
      (AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap v.hom B.polarized.dual A.polarized.dual)
      A.polarized.polarization.isogeny.hom B.polarized.polarization.isogeny.hom
      n hfv hdual f.polarization
  · intro a
    apply (cancel_epi f.isogeny.hom).mp
    calc
      f.isogeny.hom ≫ (v.hom ≫ A.action.map a) =
          (f.isogeny.hom ≫ v.hom) ≫ A.action.map a := (Category.assoc _ _ _).symm
      _ = ((𝟙 A.polarized.abelian.scheme) ^ n) ≫ A.action.map a := by rw [hfv]
      _ = A.action.map a ≫ (𝟙 A.polarized.abelian.scheme) ^ n := by
        rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
      _ = A.action.map a ≫ (f.isogeny.hom ≫ v.hom) := by rw [hfv]
      _ = f.isogeny.hom ≫ (B.action.map a ≫ v.hom) := by
        rw [← Category.assoc, ← f.action a, Category.assoc]

theorem exists_paired_pel_quotient (f : AbelianScheme.IsogenyQuotient.Intrinsic.PELBaseChange.Construction.NativePELQuotient A B n)
    (hn : 0 < n) (hmod : Nat.ModEq N n 1)
    (hker : ∀ (X : Over T.left)
      (x : X ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f.isogeny.hom), x ^ n = 1) :
    ∃ q : PairedPELQuotient A B n, q.forward = f := by
  obtain ⟨v, hfv, hvf, _⟩ := AbelianScheme.IsogenyQuotient.ScalarComplement.Construction.exists_isogeny_scalar_complement f.isogeny n hn hker T.hom
  exact ⟨{
    forward := f
    reverse := scalarComplementPELQuotient f v hn hmod hfv hvf
    forward_reverse := hfv
    reverse_forward := hvf }, rfl⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELQuotients
