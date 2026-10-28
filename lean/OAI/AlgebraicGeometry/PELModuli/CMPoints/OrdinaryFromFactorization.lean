import OAI.AlgebraicGeometry.PELModuli.CMPoints.TorsionFactorIso
import OAI.AlgebraicGeometry.PELModuli.CMPoints.FlattenTorsionFactors
import OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryCM

/-! # Ordinary From Factorization -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryFromFactorization

noncomputable section

/-! The original polarized fiber is ordinary whenever its actual
prime-to-q scalar splitting has full height-one coefficient factors.
No polarizations on the auxiliary factors are required. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ordinary_count_of_scalar_factor_heightOne
    {k E K I : Type} [Field k] [Field E] [NumberField E] [Algebra ℚ E]
    [IsGalois ℚ E] [Field K] [NumberField K] [Fintype I]
    {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime] [IsAlgClosed k] [CharP k q]
    (j : Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
    {g N : ℕ} {δ : Fin g → ℕ} {d : I → ℕ}
    (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
    (B : ∀ i, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (d i) (Spec (.of k)))
    (ρ : ∀ i, AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (B i))
    (D : TorsionFactorIso.AbelianScalarFactorization P.abelian B)
    (hgood : q.Coprime (∏ i, δ i)) (hD : q.Coprime D.multiplier)
    (hdegree : Fintype.card I * Module.finrank ℚ E = 2 * g)
    (hh : ∀ i τ, BlocksProjectors.BlockHasHeight (B i) (ρ i) (j.localCharacter iota τ) 1) :
    Nat.card (P.abelian.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ g := by
  let : Fintype Gal(E/ℚ) := Fintype.ofFinite _
  have hex (i : I) := OrdinaryCM.torsion_heightOne_decomposition j iota hsplit (B i) (ρ i)
    (PolarizedTorsionFiniteness.scalar_factor_torsion_finite_locally_free D
      (PolarizedTorsionFiniteness.polarized_torsion_finite_locally_free P (Fact.out : q.Prime).pos) hD i) (hh i)
  choose G he using hex
  let e (i : I) := Classical.choice (he i)
  let ef := FlattenTorsionFactors.flattenPiGroupIso (fun i => TorsionFactorIso.torsionCommFunctor (B i) q)
    (fun i τ => OrdinaryFromFactors.finiteGroupPointFunctor ((G i τ).level 1)) e
  have hcard : Fintype.card (I × Gal(E/ℚ)) = 2 * g := by
    rw [Fintype.card_prod]
    have hG : Fintype.card Gal(E/ℚ) = Module.finrank ℚ E :=
      Fintype.card_eq_nat_card.trans (IsGalois.card_aut_eq_finrank ℚ E)
    rw [hG]
    exact hdegree
  exact OrdinaryFromFactors.ordinary_count_of_torsion_heightOne_decomposition P hgood
    (fun z : I × Gal(E/ℚ) => G z.1 z.2) hcard (D.torsionFactorIso q hD ≪≫ ef)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryFromFactorization
