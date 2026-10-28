import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelOf
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification

/-! # Prescribed Map Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedMapKernel

noncomputable section

/-! Restrictions of the genuine quotient maps whose full kernels are
the independently prescribed canonical kernels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelOf.Components OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelOf.Containment

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
variable (n s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
variable (H : ∀ v : Fin s, AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))
variable {C : Over (Spec (.of k))} [GrpObj C] (f : A.abelian.scheme ⟶ C)
variable (hf : ∀ (T : Over (Spec (.of k))) (a : T ⟶ A.abelian.scheme),
  a ≫ f = 1 ↔ AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n s labels H T a)

include hf in
theorem prescribed_map_chosen_factor {m : ℕ} (hnm : n ≤ m) (v : Fin s)
    (T : Over (Spec (.of k))) (a : T ⟶ A.abelian.scheme)
    (hs : a ≫ ρ.map (j.projector iota hsplit m (labels (v, false))) = a)
    (ha : a ≫ f = 1) :
    ∃ h : T ⟶ (H v).group.X,
      h ≫ (H v).inclusion.hom.hom ≫
        AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n (labels (v, false)) = a :=
  PrescribedKernelOf.Components.prescribed_chosen_component_higher j iota hsplit A ρ n s labels H hnm v T a hs ((hf T a).mp ha)

include hf in
theorem prescribed_map_chosen_killed (v : Fin s)
    (T : Over (Spec (.of k))) (h : T ⟶ (H v).group.X) :
    (h ≫ (H v).inclusion.hom.hom ≫
      AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n (labels (v, false))) ≫ f = 1 :=
  (hf T _).mpr (PrescribedKernelOf.Containment.prescribed_full_kernel_contains_chosen j iota hsplit A ρ n s labels H v T h)

include hf in
theorem prescribed_map_restricted_kernel (v : Fin s) {Et : Over (Spec (.of k))}
    (ein : Et ⟶ A.abelian.scheme) [Mono ein] (h : (H v).group.X ⟶ Et) [Mono h]
    (hsquare : h ≫ ein = (H v).inclusion.hom.hom ≫
      AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n (labels (v, false)))
    {m : ℕ} (hnm : n ≤ m)
    (hsupport : ein ≫ ρ.map (j.projector iota hsplit m (labels (v, false))) = ein) :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel (ein ≫ f) h := by
  intro T a
  constructor
  · intro ha
    obtain ⟨b, hb⟩ := prescribed_map_chosen_factor j iota hsplit A ρ n s labels H f hf hnm v
      T (a ≫ ein) (by rw [Category.assoc, hsupport]) ((Category.assoc _ _ _).trans ha)
    refine ⟨b, (cancel_mono ein).mp ?_, ?_⟩
    · rw [Category.assoc, hsquare]
      exact hb
    · intro c hc
      apply (cancel_mono h).mp
      apply (cancel_mono ein).mp
      rw [hc, Category.assoc, hsquare]
      exact hb.symm
  · rintro ⟨b, rfl, _⟩
    have hk := prescribed_map_chosen_killed j iota hsplit A ρ n s labels H f hf v T b
    rw [← hsquare] at hk
    simpa only [Category.assoc] using hk

variable [NumberField.IsCMField E]
variable {r : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (r + 1)}
variable {arithmeticEmbedding : E →+* K}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P arithmeticEmbedding N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ}
variable (D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P arithmeticEmbedding κ M U B q)
variable {x y : D.OrdinaryPoint} {multiplier : ℕ}
variable {kernel : ∀ (T : Over D.integralGeometricBase.left),
  (T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme) → Prop}

theorem prescribed_quotient_kernel_iff
    (Q : D.PrescribedOrdinaryQuotient x multiplier kernel y)
    (T : Over D.integralGeometricBase.left)
    (a : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme) :
    a ≫ Q.quotient.isogeny.hom = 1 ↔ kernel T a := by
  have : IsClosedImmersion Q.inclusion.left := Q.closed
  have : Mono Q.inclusion := Over.mono_of_mono_left _
  rw [← Q.realizes T a]
  constructor
  · intro ha
    obtain ⟨h, hh, _⟩ := (Q.quotient.kernel T a).mp ha
    exact ⟨h, hh⟩
  · rintro ⟨h, hh⟩
    apply (Q.quotient.kernel T a).mpr
    refine ⟨h, hh, ?_⟩
    intro b hb
    exact (cancel_mono Q.inclusion).mp (hb.trans hh.symm)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedMapKernel
