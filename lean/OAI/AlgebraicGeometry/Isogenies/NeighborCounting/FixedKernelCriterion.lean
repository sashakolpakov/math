import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SpecialKernelPresentations

/-! # Fixed Kernel Criterion -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

section

/-! A named all-test-scheme kernel condition on a fixed component. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

def Intrinsic.Neighbors.KernelPresentation.KernelOnFixed {S : Scheme} {A B : Over S} [GrpObj B]
    (K : Intrinsic.Neighbors.KernelPresentation A) (f : A ⟶ B) (p : A ⟶ A) : Prop :=
  ∀ (T : Over S) (a : T ⟶ A), a ≫ p = a →
    (a ≫ f = 1 ↔ ∃ h : T ⟶ K.carrier, h ≫ K.inclusion = a)

end

/-! A factorization comparison transports the full fixed-component kernel. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem Intrinsic.Neighbors.KernelPresentation.KernelOnFixed.of_factor_iff
    {S : Scheme} {A B : Over S} [GrpObj B]
    {K L : Intrinsic.Neighbors.KernelPresentation A} {f : A ⟶ B} {p : A ⟶ A}
    (h : K.KernelOnFixed f p)
    (hc : ∀ (T : Over S) (a : T ⟶ A),
      (∃ k : T ⟶ K.carrier, k ≫ K.inclusion = a) ↔
        ∃ k : T ⟶ L.carrier, k ≫ L.inclusion = a) :
    L.KernelOnFixed f p :=
  fun T a ha => (h T a ha).trans (hc T a)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
