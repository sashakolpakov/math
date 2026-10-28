import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Polarized
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Embedded

/-! # Polarized Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizedTransport.Construction

noncomputable section

/-! Exact full-kernel Frobenius transport with its abelian comparison
supplied explicitly and proved equal to the full polarized component. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] [IsAlgClosed k] [CharP k q]
variable {g N : ℕ} {δ : Fin g → ℕ}
variable (A B : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N (Spec (.of k)))

variable (e : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso (A.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime)
      (Spec (CommRingCat.of k)) (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))) B)
variable (c : PolarizedComponents.Construction.EquivariantAbelianIso (CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A.polarized.abelian)
  B.polarized.abelian (CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k A.polarized.abelian A.action) B.action)
variable (hc : c = PolarizedComponents.Construction.polarizedBaseChangeAbelianComparison A B (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime)
      (Spec (CommRingCat.of k)) (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q))) e)
variable (n r : ℕ) (labels : (Fin r × Bool) ≃ Gal(E/ℚ))
variable (H : ∀ v : Fin r, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
  (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A.polarized A.action (labels (v, false)) n))
variable (J : ∀ v : Fin r, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
  (CMPointsAt.Construction.l45ChosenBlock j iota hsplit B.polarized B.action (labels (v, false)) n))
variable (eH : ∀ v, (Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime)
      (Spec (CommRingCat.of k)) (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))).obj (H v).group.X ≅ (J v).group.X)
variable (heH : ∀ v, (eH v).hom ≫ (J v).inclusion.hom.hom =
  (Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime)
      (Spec (CommRingCat.of k)) (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))).map (H v).inclusion.hom.hom ≫
    (ChosenSourceIso.Construction.frobeniusSourceBlockIso j iota hsplit k A.polarized.abelian B.polarized.abelian
      A.action B.action c n (labels (v, false))).hom.hom.hom)

include hc heH in
/-- The full independent prescription satisfies the packaged all-test transport relation. -/
theorem prescribedFullKernel_frobeniusTransport :
    Embedded.Construction.FrobeniusKernelTransport A.polarized.abelian B.polarized.abelian c.abelian
      (Prescription.Construction.prescribedFullKernel j iota hsplit A.polarized A.action n r labels H)
      (Prescription.Construction.prescribedFullKernel j iota hsplit B.polarized B.action n r labels J) :=
  Polarized.Construction.prescribedFullKernel_polarizedFrobenius j iota hsplit A B e c hc n r labels H J eH heH

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizedTransport.Construction
