import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescribed

/-! # Mixed Kernels -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedKernels

noncomputable section

/-!
The mixed active kernel is obtained by taking the multiplicative quotient
and then an etale kernel. The projection onto the etale factor is derived
from the first quotient killing the multiplicative subgroup. All kernel
identities are universal on test schemes and retain infinitesimal sections.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescribed.Construction

variable {S : Scheme.{u}} {A B C M E H : Over S}
variable [GrpObj A] [GrpObj B] [GrpObj C] [GrpObj M] [GrpObj E]

def multiplicativeInclusion : M ⟶ M ⊗ E := lift (𝟙 M) 1
def etaleInclusion : E ⟶ M ⊗ E := lift 1 (𝟙 E)

theorem split_identity :
    (fst M E ≫ multiplicativeInclusion) * (snd M E ≫ etaleInclusion) = 𝟙 (M ⊗ E) := by
  apply hom_ext
  · simp [multiplicativeInclusion, etaleInclusion, MonObj.mul_comp]
  · simp [multiplicativeInclusion, etaleInclusion, MonObj.mul_comp]

/-- The map of the etale factor induced by the actual first quotient. -/
def etaleImage (b : M ⊗ E ⟶ A) (f : A ⟶ B) : E ⟶ B :=
  etaleInclusion ≫ b ≫ f

/-- Killing the multiplicative factor forces the restriction of the first
quotient to factor through the actual etale projection. -/
theorem quotient_restricts_to_etale_projection
    (b : M ⊗ E ⟶ A) (f : A ⟶ B) [IsMonHom b] [IsMonHom f]
    (hkill : multiplicativeInclusion ≫ b ≫ f = 1) :
    b ≫ f = snd M E ≫ etaleImage b f := by
  calc
    b ≫ f = (𝟙 (M ⊗ E)) ≫ (b ≫ f) := (Category.id_comp _).symm
    _ = ((fst M E ≫ multiplicativeInclusion) *
        (snd M E ≫ etaleInclusion)) ≫ (b ≫ f) :=
      congrArg (fun z => z ≫ (b ≫ f)) split_identity.symm
    _ = snd M E ≫ etaleImage b f := by
      rw [MonObj.mul_comp]
      simp only [Category.assoc, hkill, MonObj.comp_one, one_mul, etaleImage]

omit [GrpObj A] [GrpObj B] [GrpObj M] [GrpObj E] in
/-- Preimage of an etale subgroup under the product projection is its
product with the multiplicative factor, with the unique factorization proved. -/
theorem product_projection_prescribedKernel
    (g : E ⟶ C) (e : H ⟶ E) [Mono e] (hk : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel g e) :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel (snd M E ≫ g) (𝟙 M ⊗ₘ e) := by
  intro T a
  constructor
  · intro ha
    obtain ⟨h, hh, huniq⟩ := (hk T (a ≫ snd M E)).mp ((Category.assoc _ _ _).trans ha)
    refine ⟨lift (a ≫ fst M E) h, ?_, ?_⟩
    · apply hom_ext
      · simp only [Category.assoc, tensorHom_fst, Category.comp_id, lift_fst]
      · simp only [Category.assoc, tensorHom_snd, lift_snd_assoc]
        exact hh
    · intro k hk
      apply hom_ext
      · have ht := congrArg (fun z => z ≫ fst M E) hk
        simpa only [Category.assoc, tensorHom_fst, Category.comp_id, lift_fst] using ht
      · have ht := congrArg (fun z => z ≫ snd M E) hk
        have hkH : (k ≫ snd M H) ≫ e = a ≫ snd M E := by
          simpa only [Category.assoc, tensorHom_snd] using ht
        simpa only [lift_snd] using huniq (k ≫ snd M H) hkH
  · rintro ⟨k, hfactor, _⟩
    have hkill : e ≫ g = 1 := AbelianScheme.FrobeniusKernel.Prescribed.Construction.prescribedKernel_kills g e hk
    rw [← hfactor, Category.assoc, tensorHom_snd_assoc, hkill,
      MonObj.comp_one, MonObj.comp_one]

/-- A multiplicative quotient followed by an etale active kernel has the
combined product as its active preimage. The first projection equation
is proved from the actual killed subgroup, rather than assumed. -/
theorem active_composite_prescribedKernel
    (b : M ⊗ E ⟶ A) (f : A ⟶ B) (g : B ⟶ C)
    [IsMonHom b] [IsMonHom f]
    (hkill : multiplicativeInclusion ≫ b ≫ f = 1)
    (e : H ⟶ E) [Mono e] (hetale : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel (etaleImage b f ≫ g) e) :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel (b ≫ f ≫ g) (𝟙 M ⊗ₘ e) := by
  have heq : b ≫ f ≫ g = snd M E ≫ (etaleImage b f ≫ g) := by
    rw [← Category.assoc, quotient_restricts_to_etale_projection b f hkill, Category.assoc]
  rw [heq]
  exact product_projection_prescribedKernel _ e hetale

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedKernels
