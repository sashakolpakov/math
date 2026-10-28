import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockKernelExhaustion

/-! # Ambient Kernel Factors -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AmbientKernelFactors

noncomputable section

/-! A computed kernel inside an embedded torsion block gives the
corresponding factorization criterion inside the original abelian source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem ambient_kernel_factor_iff {S : Scheme} {A B C H T : Over S} [GrpObj B]
    (f : A ⟶ B) (k : C ⟶ A) [Mono k] (i : H ⟶ C) [Mono i]
    (hi : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel (k ≫ f) i)
    (x : T ⟶ A) (c : T ⟶ C) (hc : c ≫ k = x) :
    x ≫ f = 1 ↔ ∃ h : T ⟶ H, h ≫ i ≫ k = x := by
  constructor
  · intro hx
    have hz : c ≫ (k ≫ f) = 1 :=
      (Category.assoc c k f).symm.trans ((congrArg (fun u => u ≫ f) hc).trans hx)
    obtain ⟨h, hh, _⟩ := (hi T c).mp hz
    exact ⟨h, (Category.assoc h i k).symm.trans ((congrArg (fun u => u ≫ k) hh).trans hc)⟩
  · rintro ⟨h, hh⟩
    have hh' : h ≫ i = c :=
      (cancel_mono k).mp ((Category.assoc h i k).trans (hh.trans hc.symm))
    have hz : c ≫ (k ≫ f) = 1 := (hi T c).mpr
      ⟨h, hh', fun b hb => (cancel_mono i).mp (hb.trans hh'.symm)⟩
    exact (congrArg (fun u => u ≫ f) hc).symm.trans ((Category.assoc c k f).trans hz)

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A) (n : ℕ) (τ : Gal(E/ℚ))

theorem native_block_kernel_factor {B H : Over S} [GrpObj B]
    (f : A.scheme ⟶ B)
    (i : H ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (ρ.map (j.projector iota hsplit n τ))) [Mono i]
    (hi : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n τ)) ≫ f) i)
    (T : Over S) (x : T ⟶ A.scheme) (hx : x ^ (q ^ n) = 1)
    (hp : x ≫ ρ.map (j.projector iota hsplit n τ) = x) :
    x ≫ f = 1 ↔ ∃ h : T ⟶ H,
      h ≫ i ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n τ)) = x :=
  ambient_kernel_factor_iff f
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n τ))) i hi x
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockLift (q ^ n) (ρ.map (j.projector iota hsplit n τ)) x hx hp)
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockLift_inclusion _ _ _ _ _)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AmbientKernelFactors
