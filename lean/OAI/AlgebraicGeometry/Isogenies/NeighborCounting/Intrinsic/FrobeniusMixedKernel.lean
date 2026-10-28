import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockKernelExhaustion
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FrobeniusKernelExhaustion

/-! # Frobenius Mixed Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.FrobeniusMixedKernel

noncomputable section

/-! The q-block computation exhausts the mixed kernel in every native
higher active block. The complementary Frobenius map proves the needed
q-torsion bound from the second quotient's one-step etale kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedKernelExhaustion OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockKernelExhaustion

variable {E K k : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable [Field k] [CharP k q] [PerfectRing k q]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k)))
variable (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
variable {n : ℕ} (hn : 1 ≤ n) (τ : Gal(E/ℚ))

abbrev nativeFrobenius := Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q Fact.out
  (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) A.scheme

abbrev nativeTwist := Picard.Homomorphisms.Frobenius.Construction.frobeniusTwist q Fact.out
  (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) A.scheme

abbrev twistedProjector :=
  (Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q Fact.out (Spec (.of k))
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))).map (σ.map (j.projector iota hsplit n τ))

theorem native_frobenius_kernel_from_qblock
    {Et H C Q : Over (Spec (.of k))} [GrpObj C]
    (sourceEtale : Et ⟶ A.scheme) (targetEtale : H ⟶ nativeTwist A)
    (etaleIso : Et ≅ H)
    (hplane : etaleIso.hom ≫ targetEtale = sourceEtale ≫ nativeFrobenius A)
    (hetale : sourceEtale ^ q = 1) (g : nativeTwist A ⟶ C)
    (hsecond : ∀ (T : Over (Spec (.of k))) (b : T ⟶ nativeTwist A),
      b ≫ twistedProjector j iota hsplit A σ (n := n) τ = b → b ≫ g = 1 →
        ∃ h : T ⟶ H, h ≫ targetEtale = b)
    (u : Q ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1) (σ.map (j.projector iota hsplit 1 τ)))
    (hu : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (σ.map (j.projector iota hsplit 1 τ)) ≫ nativeFrobenius A ≫ g) u) :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (σ.map (j.projector iota hsplit n τ)) ≫ nativeFrobenius A ≫ g)
      (u ≫ BlockKernelExhaustion.nativeBlockEmbedding j iota hsplit A σ hn τ) := by
  have hv := MixedKernelExhaustion.complement_kills_transported_torsion (nativeFrobenius A) (Picard.Homomorphisms.Verschiebung.Construction.verschiebung q k A.scheme)
    q (Picard.Homomorphisms.Verschiebung.Construction.frobenius_comp_verschiebung q k A.scheme) sourceEtale targetEtale etaleIso hplane hetale
  have hb : ∀ (T : Over (Spec (.of k))) (a : T ⟶ A.scheme),
      a ≫ σ.map (j.projector iota hsplit n τ) = a → a ≫ (nativeFrobenius A ≫ g) = 1 →
        a ^ (q ^ 1) = 1 := by
    intro T a ha hk
    rw [pow_one]
    exact MixedKernelExhaustion.supported_composite_kernel_killed (nativeFrobenius A) (Picard.Homomorphisms.Verschiebung.Construction.verschiebung q k A.scheme) g
      q (Picard.Homomorphisms.Verschiebung.Construction.frobenius_comp_verschiebung q k A.scheme) (σ.map (j.projector iota hsplit n τ))
      (twistedProjector j iota hsplit A σ (n := n) τ)
      ((Picard.Homomorphisms.Group.Construction.relativeFrobeniusNat q Fact.out (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q))).naturality _)
      targetEtale hv hsecond T a ha hk
  exact BlockKernelExhaustion.native_high_kernel_from_low j iota hsplit A σ hn τ (nativeFrobenius A ≫ g) hb u hu

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.FrobeniusMixedKernel
