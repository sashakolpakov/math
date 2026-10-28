import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TupleKernelPoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAction
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAt

/-! # Kernel Points -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelPoints

noncomputable section

/-! The original native FrobeniusKernel complete kernel has exactly the relative
product of its chosen and opposite subgroup images. The equality follows
from its actual coefficient splitting and represents all test points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TupleKernelPoints

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
variable (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
variable (PEL : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PEL.abelian)
variable (n s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
variable (P : ∀ v : Fin s, AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates (.of k)
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) n))
variable (H : ∀ v : Fin s, AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) n))
variable (hdual : ∀ v : Fin s, PELModuli.CMPoints.DualityPairing.PolarizationDuality PEL ρ
  (j.localCharacter iota (labels (v, false))) (j.localCharacter iota (labels (v, true))))

abbrev chosenAmbientInclusion (v : Fin s) :=
  (H v).inclusion.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PEL.abelian ρ n (labels (v, false))

abbrev oppositeAmbientInclusion (v : Fin s) :=
  (AbelianScheme.FrobeniusKernel.CMPointsAction.Construction.l45ChosenOppositeInclusion j iota hsplit PEL ρ n s labels P H hdual v).hom.hom ≫
    AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PEL.abelian ρ n (labels (v, true))

theorem native_full_pair_formula (T : Over (Spec (.of k)))
    (a : T ⟶ (AbelianScheme.FrobeniusKernel.CMPointsKernels.Construction.l45FullChosenKernel j iota hsplit PEL ρ n s labels P H).X) :
    a ≫ AbelianScheme.FrobeniusKernel.CMPointsKernels.Construction.l45FullChosenKernelInclusion j iota hsplit PEL ρ n s labels P H hdual =
      ∏ v : Fin s,
        ((AbelianScheme.FrobeniusKernel.ProductPoints.Construction.groupBlockProductPointsEquiv s (AbelianScheme.FrobeniusKernel.CMPointsAction.Construction.l45PairedChosenFamily j iota hsplit PEL ρ n s labels P H)
          T a v ≫ fst _ _) ≫ chosenAmbientInclusion j iota hsplit PEL ρ n s labels H v) *
        ((AbelianScheme.FrobeniusKernel.ProductPoints.Construction.groupBlockProductPointsEquiv s (AbelianScheme.FrobeniusKernel.CMPointsAction.Construction.l45PairedChosenFamily j iota hsplit PEL ρ n s labels P H)
          T a v ≫ snd _ _) ≫ oppositeAmbientInclusion j iota hsplit PEL ρ n s labels P H hdual v) := by
  let : Fintype Gal(E/ℚ) := Fintype.ofFinite _
  rw [AbelianScheme.FrobeniusKernel.CMPointsAction.Construction.l45FullChosenKernelInclusion_point]
  let b := AbelianScheme.FrobeniusKernel.CMPointsAction.Construction.l45FullChosenPointBlocks j iota hsplit PEL ρ n s labels P H hdual T a
  change (∏ τ, (b τ).val) = _
  rw [← Fintype.prod_equiv labels (fun v => (b (labels v)).val) (fun τ => (b τ).val)
    (fun _ => rfl), Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro v _
  rw [Fintype.prod_bool]
  dsimp only [b]
  rw [AbelianScheme.FrobeniusKernel.CMPointsAction.Construction.l45FullChosenPointBlocks_true, AbelianScheme.FrobeniusKernel.CMPointsAction.Construction.l45FullChosenPointBlocks_false,
    AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion_point, AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion_point]
  simpa only [chosenAmbientInclusion, oppositeAmbientInclusion, Category.assoc] using mul_comm
    (((AbelianScheme.FrobeniusKernel.ProductPoints.Construction.groupBlockProductPointsEquiv s (AbelianScheme.FrobeniusKernel.CMPointsAction.Construction.l45PairedChosenFamily j iota hsplit PEL ρ n s labels P H)
      T a v ≫ snd _ _) ≫
      (AbelianScheme.FrobeniusKernel.CMPointsAction.Construction.l45ChosenOppositeInclusion j iota hsplit PEL ρ n s labels P H hdual v).hom.hom) ≫
        AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PEL.abelian ρ n (labels (v, true)))
    (((AbelianScheme.FrobeniusKernel.ProductPoints.Construction.groupBlockProductPointsEquiv s (AbelianScheme.FrobeniusKernel.CMPointsAction.Construction.l45PairedChosenFamily j iota hsplit PEL ρ n s labels P H)
      T a v ≫ fst _ _) ≫ (H v).inclusion.hom.hom) ≫
        AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PEL.abelian ρ n (labels (v, false)))

theorem native_full_kernel_family {X : Over (Spec (.of k))} :
    Kernel.Base.fixedKernelFamily (P := X)
      (AbelianScheme.FrobeniusKernel.CMPointsKernels.Construction.l45FullChosenKernelInclusion j iota hsplit PEL ρ n s labels P H hdual) =
      AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel s (fun v => AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct
        (Kernel.Base.fixedKernelFamily (chosenAmbientInclusion j iota hsplit PEL ρ n s labels H v))
        (Kernel.Base.fixedKernelFamily (oppositeAmbientInclusion j iota hsplit PEL ρ n s labels P H hdual v))) := by
  exact @TupleKernelPoints.fixed_paired_product_family _ _ X _ _ s (fun v => (H v).group)
    (chosenAmbientInclusion j iota hsplit PEL ρ n s labels H)
    (fun _ => inferInstance)
    (fun v => (P v).annihilatorGroup (H v).coordinates (H v).inclusion)
    (oppositeAmbientInclusion j iota hsplit PEL ρ n s labels P H hdual)
    (fun _ => inferInstance)
    (AbelianScheme.FrobeniusKernel.CMPointsKernels.Construction.l45FullChosenKernelInclusion j iota hsplit PEL ρ n s labels P H hdual)
    (AbelianScheme.FrobeniusKernel.CMPointsKernels.Construction.l45FullChosenKernelInclusion_isMonHom j iota hsplit PEL ρ n s labels P H hdual)
    (native_full_pair_formula j iota hsplit PEL ρ n s labels P H hdual)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelPoints
