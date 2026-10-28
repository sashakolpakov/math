import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockBigPresentation
import OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryFromFactors
import OAI.AlgebraicGeometry.PELModuli.CMPoints.CoefficientBlockCard

/-! # Ordinary CM -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryCM

noncomputable section

section

/-! A full coefficient-field action at a split prime gives ordinary
specialization. The height-one factors and the whole-site torsion
product are constructed from the actual coefficient blocks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k E K : Type} [Field k] [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

include hsplit in
theorem torsion_heightOne_decomposition [Fintype Gal(E/ℚ)]
    (ht : PolarizedTorsionFiniteness.TorsionFiniteLocallyFree A q)
    (hh : ∀ τ : Gal(E/ℚ), BlocksProjectors.BlockHasHeight A ρ (j.localCharacter iota τ) 1) :
    ∃ G : Gal(E/ℚ) → GroupSchemes.FiniteEtale.PDivisibleGroup k q 1,
      Nonempty (A.torsionFunctor q ≅ FlattenTorsionFactors.piGroupFunctor (fun τ => OrdinaryFromFactors.finiteGroupPointFunctor ((G τ).level 1))) := by
  have hex (τ : Gal(E/ℚ)) := BlockBigPresentation.block_big_presentation_of_height j iota hsplit A ρ ht τ 1 (hh τ)
  choose G he using hex
  let e := fun τ => Classical.choice (he τ)
  have hn : A.torsionFunctor q = A.torsionFunctor (q ^ 1) := by rw [pow_one]
  refine ⟨G, ⟨eqToIso hn ≪≫ BlockDecomposition.torsionBlockIso j iota hsplit A ρ 1 ≪≫ ?_⟩⟩
  refine NatIso.ofComponents (fun T =>
    (MulEquiv.piCongrRight (fun τ => (((e τ 1).app T).groupIsoToMulEquiv).symm)).toGrpIso) ?_
  intro T U f
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  funext τ
  exact ((e τ 1).inv.naturality_apply f (x τ))

include hsplit in
theorem ordinary_count_of_heightOne_blocks [IsAlgClosed k] [CharP k q] [IsGalois ℚ E]
    {N : ℕ} {δ : Fin g → ℕ}
    (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) P.abelian)
    (hgood : q.Coprime (∏ i, δ i)) (hdegree : Module.finrank ℚ E = 2 * g)
    (hh : ∀ τ : Gal(E/ℚ), BlocksProjectors.BlockHasHeight P.abelian ρ (j.localCharacter iota τ) 1) :
    Nat.card (P.abelian.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ g := by
  let : Fintype Gal(E/ℚ) := Fintype.ofFinite _
  obtain ⟨G, ⟨e⟩⟩ := torsion_heightOne_decomposition j iota hsplit P.abelian ρ
    (PolarizedTorsionFiniteness.polarized_torsion_finite_locally_free P (Fact.out : q.Prime).pos) hh
  have hcard : Fintype.card Gal(E/ℚ) = 2 * g :=
    Fintype.card_eq_nat_card.trans ((IsGalois.card_aut_eq_finrank ℚ E).trans hdegree)
  exact OrdinaryFromFactors.ordinary_count_of_torsion_heightOne_decomposition P hgood G hcard e

end

section

/-! Ordinary specialization for an actual relative full coefficient
action. The prime bound comes from the complex exponential lattice;
height-one blocks, their torsion product, and the ordinary count are
all conclusions. No ordinary-specialization premise is used. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_fullCM_ordinary_bound
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    [Field K] [NumberField K] {κ : K →+* ℂ} (iota : E →+* K)
    {S : Scheme.{0}} [ConnectedSpace S] {g N : ℕ} {δ : Fin g → ℕ}
    (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) P.abelian)
    (pC : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S)
    (PC : Foundations.Scheme.SmoothProjective.ProjectivePresentation (P.abelian.pullback pC).scheme.left
      (P.abelian.pullback pC).scheme.hom)
    (hdegree : Module.finrank ℚ E = 2 * g) :
    ∃ D : ℕ, 0 < D ∧ ∀ (q : ℕ) (hq : q.Prime),
      letI : Fact q.Prime := ⟨hq⟩
      ∀ j : Arithmetic.QadicChoice K κ q, j.HasSplitCoordinates iota → D < q →
        q.Coprime (∏ i, δ i) →
        ∀ (k : Type) [Field k] [IsAlgClosed k] [CharP k q] (p : Spec (.of k) ⟶ S),
          Nat.card ((P.abelian.pullback p).torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ g := by
  obtain ⟨D, hD, hcard⟩ := CoefficientBlockCard.exists_complex_coefficient_block_bound (κ := κ) iota
    (P.abelian.pullback pC) PC (ρ.pullback pC) 1 (by simpa only [Nat.mul_one] using hdegree)
  refine ⟨D, hD, fun q hq => ?_⟩
  let : Fact q.Prime := ⟨hq⟩
  intro j hsplit hb hgood k hk hclosed hchar p
  have hh (τ : Gal(E/ℚ)) :
      BlocksProjectors.BlockHasHeight (P.abelian.pullback p) (ρ.pullback p) (j.localCharacter iota τ) 1 := by
    apply Multiplication.blockHasHeight_of_torsion_finite_locally_free j iota hsplit P.abelian
      (PolarizedTorsionFiniteness.polarized_torsion_finite_locally_free P hq.pos) ρ pC τ 1 _ p
    intro n
    simpa only [Nat.one_mul, Nat.mul_one] using hcard q hq j hsplit hb n τ
  exact ordinary_count_of_heightOne_blocks j iota hsplit (P.pullback p)
    (ρ.pullback p) hgood hdegree hh

end

/-! A full coefficient action supplies height-one blocks without
choosing a polarization on the individual CM factor. The eventual
ordinary count can use the original PEL fiber's polarization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_fullCM_heightOne_bound
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    [Field K] [NumberField K] {κ : K →+* ℂ} (iota : E →+* K)
    {S : Scheme.{0}} [ConnectedSpace S] {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (pC : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S)
    (PC : Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.pullback pC).scheme.left (A.pullback pC).scheme.hom)
    (hdegree : Module.finrank ℚ E = 2 * g) :
    ∃ D : ℕ, 0 < D ∧ ∀ (q : ℕ) (hq : q.Prime),
      letI : Fact q.Prime := ⟨hq⟩
      ∀ j : Arithmetic.QadicChoice K κ q, j.HasSplitCoordinates iota → D < q → PolarizedTorsionFiniteness.TorsionFiniteLocallyFree A q →
        ∀ (k : Type) [Field k] (p : Spec (.of k) ⟶ S) (τ : Gal(E/ℚ)),
          BlocksProjectors.BlockHasHeight (A.pullback p) (ρ.pullback p) (j.localCharacter iota τ) 1 := by
  obtain ⟨D, hD, hcard⟩ := CoefficientBlockCard.exists_complex_coefficient_block_bound (κ := κ) iota
    (A.pullback pC) PC (ρ.pullback pC) 1 (by simpa only [Nat.mul_one] using hdegree)
  refine ⟨D, hD, fun q hq => ?_⟩
  let : Fact q.Prime := ⟨hq⟩
  intro j hsplit hb ht k hk p τ
  apply Multiplication.blockHasHeight_of_torsion_finite_locally_free j iota hsplit A ht ρ pC τ 1 _ p
  intro n
  simpa only [Nat.one_mul, Nat.mul_one] using hcard q hq j hsplit hb n τ

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryCM
