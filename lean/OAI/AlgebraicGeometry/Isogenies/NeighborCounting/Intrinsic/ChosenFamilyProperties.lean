import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FamilyTransport
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAt

/-! # Chosen Family Properties -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChosenFamilyProperties.IntrinsicFamily

noncomputable section

/-! The actual CMPoints character-block inclusion proves both the power
bound and coefficient support of every embedded chosen subgroup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAt.Construction

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {S : Scheme} {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S)
variable (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
variable (n : ℕ) (τ : Gal(E/ℚ))
variable {H : Grp (Over S)} {P : Over S}
variable (i : H ⟶ (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A σ n τ).toGrp)

theorem original_block_family_bound :
    (Kernel.Base.fixedKernelFamily (P := P) (i.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A σ n τ)).KilledBy (q ^ n) ∧
      AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn (Kernel.Base.fixedKernelFamily (P := P) (i.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A σ n τ))
        (σ.map (j.projector iota hsplit n τ)) := by
  have hp (T : Over S) (b : T ⟶ H.X) :
      ((b ≫ i.hom.hom) ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A σ n τ) ^ (q ^ n) = 1 ∧
        (((b ≫ i.hom.hom) ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A σ n τ) ≫
          σ.map (j.projector iota hsplit n τ)) =
            (b ≫ i.hom.hom) ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A σ n τ :=
    (PELModuli.CMPoints.BlocksProjectors.mem_block_iff_fixed j iota hsplit A σ n τ T _).mp
      (((AbelianScheme.FrobeniusKernel.CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A σ n τ).hom.app (.op T) (b ≫ i.hom.hom)).property)
  constructor
  · rintro T t a ⟨b, rfl⟩
    change (b ≫ (i.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A σ n τ)) ^ (q ^ n) = 1
    simpa only [Category.assoc] using (hp T b).1
  · rintro T t a ⟨b, rfl⟩
    change (b ≫ (i.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A σ n τ)) ≫
      σ.map (j.projector iota hsplit n τ) =
        b ≫ (i.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A σ n τ)
    simpa only [Category.assoc] using (hp T b).2

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChosenFamilyProperties.IntrinsicFamily
