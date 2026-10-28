import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalBlockComponents
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsBlockPointsTransport

/-! # Prescribed Source Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedSourcePoints.Construction

noncomputable section

/-! The exact original prescribed components retain an equivariant
source homomorphism and the actual chosen subgroup inclusion square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
variable (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B.abelian)
variable (f : A.abelian.scheme ⟶ B.abelian.scheme) [IsMonHom f]
variable (hf : ∀ z : NumberField.RingOfIntegers E, ρ.map z ≫ f = f ≫ σ.map z)
variable (n : ℕ) (τ : Gal(E/ℚ))

include hf in
theorem prescribedBlockComponent_sourceMap (T : Over (Spec (.of k)))
    (x : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) :
    (PELModuli.CMPoints.DualityPairing.homOnTorsion A.abelian B.abelian f (q ^ n)).app (.op T)
      (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n τ T x) =
      Prescription.Construction.prescribedBlockComponent j iota hsplit B σ n τ T
        ((PELModuli.CMPoints.DualityPairing.homOnTorsion A.abelian B.abelian f (q ^ n)).app (.op T) x) := by
  apply Subtype.ext
  exact (Category.assoc x.val (ρ.map (j.projector iota hsplit n τ)) f).trans
    ((congrArg (fun z => x.val ≫ z) (hf (j.projector iota hsplit n τ))).trans
      (Category.assoc x.val f (σ.map (j.projector iota hsplit n τ))).symm)

theorem canonicalOriginalBlockPoint_sourceMap (T : Over (Spec (.of k)))
    (z : T ⟶ (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n).X) :
    (PELModuli.CMPoints.DualityPairing.homOnTorsion A.abelian B.abelian f (q ^ n)).app (.op T)
      (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n τ T z) =
      CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit B σ n τ T
        (z ≫ (PointsBlockPointsTransport.Construction.l45BlockMap j iota hsplit A.abelian B.abelian ρ σ f hf n τ).hom.hom) := by
  apply Subtype.ext
  have h := congrArg (fun a : PELModuli.CMPoints.BlocksProjectors.blockPoints B.abelian σ (j.localCharacter iota τ) n T => a.val)
    (PointsBlockPointsTransport.Construction.l45BlockMap_points j iota hsplit A.abelian B.abelian ρ σ f hf n τ T z)
  exact h.symm

variable (H : FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n))
variable (J : FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (CMPointsAt.Construction.l45ChosenBlock j iota hsplit B σ τ n))
variable (l : H.group.X ⟶ J.group.X)
variable (hl : l ≫ J.inclusion.hom.hom = H.inclusion.hom.hom ≫
  (PointsBlockPointsTransport.Construction.l45BlockMap j iota hsplit A.abelian B.abelian ρ σ f hf n τ).hom.hom)

include hl in
theorem prescribedChosenPoint_sourceMap (T : Over (Spec (.of k))) (h : T ⟶ H.group.X) :
    (PELModuli.CMPoints.DualityPairing.homOnTorsion A.abelian B.abelian f (q ^ n)).app (.op T)
      (Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n τ H T h) =
      Prescription.Construction.prescribedChosenPoint j iota hsplit B σ n τ J T (h ≫ l) := by
  have hs := (Category.assoc h l J.inclusion.hom.hom).trans
    ((congrArg (fun z => h ≫ z) hl).trans (Category.assoc h H.inclusion.hom.hom _).symm)
  exact (canonicalOriginalBlockPoint_sourceMap j iota hsplit A B ρ σ f hf n τ T
    (h ≫ H.inclusion.hom.hom)).trans
      (congrArg (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit B σ n τ T) hs.symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedSourcePoints.Construction
