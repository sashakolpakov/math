import OAI.AlgebraicGeometry.PELModuli.CMPoints.RelativeHeight
import OAI.AlgebraicGeometry.PELModuli.CMPoints.PolarizedTorsionFiniteness

/-! # Multiplication -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.Multiplication

noncomputable section

/-! Exact interface for the newly identified general multiplication
theorem. This proposition concerns every positive multiplication map
on an abelian scheme, including residue characteristics dividing N.
It contains no CM, ordinary, block-height, or density conclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

/-- General abelian-scheme multiplication, required beyond the
invertible-torsion theorem TorsionQuotient. This input is documented in Dependencies.md. -/
def AbelianMultiplicationInput : Prop :=
  ∀ (S : Scheme.{0}) (g : ℕ) (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (N : ℕ), 0 < N →
    IsFinite (A.multiplication N).left ∧ Flat (A.multiplication N).left ∧
      LocallyOfFinitePresentation (A.multiplication N).left

theorem abelian_torsion_finite_locally_free (hMul : AbelianMultiplicationInput)
    {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (N : ℕ) (hN : 0 < N) :
    IsFinite (A.torsionScheme N).hom ∧ Flat (A.torsionScheme N).hom ∧
      LocallyOfFinitePresentation (A.torsionScheme N).hom := by
  obtain ⟨hf, hflat, hfp⟩ := hMul S g A N hN
  let : IsFinite (A.multiplication N).left := hf
  let : Flat (A.multiplication N).left := hflat
  let : LocallyOfFinitePresentation (A.multiplication N).left := hfp
  exact ⟨inferInstanceAs (IsFinite (CategoryTheory.Limits.pullback.snd (A.multiplication N).left η[A.scheme].left)),
    inferInstanceAs (Flat (CategoryTheory.Limits.pullback.snd (A.multiplication N).left η[A.scheme].left)),
    inferInstanceAs (LocallyOfFinitePresentation
      (CategoryTheory.Limits.pullback.snd (A.multiplication N).left η[A.scheme].left))⟩

theorem blockHasHeight_of_multiplication_input (hMul : AbelianMultiplicationInput)
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
    (j : Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
    {S : Scheme.{0}} [ConnectedSpace S] {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (pC : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S) (τ : Gal(E/ℚ)) (h : ℕ)
    (hcard : ∀ n : ℕ,
      Nat.card (BlocksProjectors.blockPoints (A.pullback pC) (ρ.pullback pC) (j.localCharacter iota τ) n
        (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) = q ^ (n * h))
    {k : Type} [Field k] (p : Spec (.of k) ⟶ S) :
    BlocksProjectors.BlockHasHeight (A.pullback p) (ρ.pullback p) (j.localCharacter iota τ) h := by
  have ht (n : ℕ) := abelian_torsion_finite_locally_free hMul A (q ^ n)
    (pow_pos (Fact.out : q.Prime).pos n)
  let : ∀ n : ℕ, IsFinite (A.torsionScheme (q ^ n)).hom := fun n => (ht n).1
  let : ∀ n : ℕ, Flat (A.torsionScheme (q ^ n)).hom := fun n => (ht n).2.1
  let : ∀ n : ℕ, LocallyOfFinitePresentation (A.torsionScheme (q ^ n)).hom := fun n => (ht n).2.2
  exact RelativeHeight.blockHasHeight_of_connected_finite_flat_torsion j iota hsplit A ρ pC τ h hcard p

theorem blockHasHeight_of_torsion_finite_locally_free
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
    (j : Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
    {S : Scheme.{0}} [ConnectedSpace S] {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (ht : PolarizedTorsionFiniteness.TorsionFiniteLocallyFree A q)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (pC : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S) (τ : Gal(E/ℚ)) (h : ℕ)
    (hcard : ∀ n : ℕ,
      Nat.card (BlocksProjectors.blockPoints (A.pullback pC) (ρ.pullback pC) (j.localCharacter iota τ) n
        (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) = q ^ (n * h))
    {k : Type} [Field k] (p : Spec (.of k) ⟶ S) :
    BlocksProjectors.BlockHasHeight (A.pullback p) (ρ.pullback p) (j.localCharacter iota τ) h := by
  let : ∀ n : ℕ, IsFinite (A.torsionScheme (q ^ n)).hom := fun n => (ht n).1
  let : ∀ n : ℕ, Flat (A.torsionScheme (q ^ n)).hom := fun n => (ht n).2.1
  let : ∀ n : ℕ, LocallyOfFinitePresentation (A.torsionScheme (q ^ n)).hom := fun n => (ht n).2.2
  exact RelativeHeight.blockHasHeight_of_connected_finite_flat_torsion j iota hsplit A ρ pC τ h hcard p

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.Multiplication
