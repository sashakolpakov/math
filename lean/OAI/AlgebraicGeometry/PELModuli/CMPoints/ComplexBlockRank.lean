import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComplexBlockCard
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComplexBlockEtale
import OAI.AlgebraicGeometry.PELModuli.CMPoints.EtaleRank

/-! # Complex Block Rank -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ComplexBlockRank

noncomputable section

/-! The complex torsion count computes the scheme-theoretic block
rank, because the actual projector block is finite etale. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

theorem complex_block_presentation_rank_eq_card (n : ℕ) (τ : Gal(E/ℚ))
    (H : GroupSchemes.FiniteEtale.FiniteCommGroupScheme ℂ)
    (e : H.scheme ≅ (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X) :
    Module.finrank ℂ H.algebra = Nat.card (BlocksProjectors.blockPoints A ρ (j.localCharacter iota τ) n
      (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) := by
  let : NeZero (q ^ n) := ⟨pow_ne_zero n (Fact.out : q.Prime).ne_zero⟩
  have hb := (ComplexBlockEtale.complex_idempotent_block_finite_etale A ρ (q ^ n)
    (j.projector iota hsplit n τ)).2
  let : Etale (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom := hb
  have : IsIso e.hom.left := inferInstanceAs
    (IsIso (((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso e).hom))
  let : Etale H.scheme.hom := by
    rw [← e.hom.w]
    infer_instance
  let ep := (Iso.homCongr (Iso.refl (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) e).trans
    (BlocksProjectors.splitBlockSchemePointsEquiv j iota hsplit A ρ n τ (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase))
  exact (EtaleRank.finite_etale_group_basePoints_rank H).trans (Nat.card_congr ep)

theorem complex_block_presentation_rank (n : ℕ) (τ : Gal(E/ℚ))
    (H : GroupSchemes.FiniteEtale.FiniteCommGroupScheme ℂ)
    (e : H.scheme ≅ (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X)
    (hcard : Nat.card (BlocksProjectors.blockPoints A ρ (j.localCharacter iota τ) n
      (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) = q ^ (3 * n)) :
    Module.finrank ℂ H.algebra = q ^ (3 * n) :=
  (complex_block_presentation_rank_eq_card j iota hsplit A ρ n τ H e).trans hcard

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ComplexBlockRank
