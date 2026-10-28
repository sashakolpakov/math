import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormBaseChange
import Mathlib.RingTheory.Trace.Defs

/-! # Trace -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Trace.Construction

noncomputable section

/-! The finite-free trace on actual affine section rings commutes with
arbitrary base change. The calculation retains the given ring maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem trace_map_of_basis
    {R S A B ι : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra S B] [Fintype ι]
    (φ : R →+* S) (f : A →+* B)
    (hf : ∀ r, f (algebraMap R A r) = algebraMap S B (φ r))
    (b : Module.Basis ι R A) (d : Module.Basis ι S B) (hd : ∀ i, d i = f (b i))
    (a : A) : Algebra.trace S B (f a) = φ (Algebra.trace R A a) := by
  classical
  rw [Algebra.trace_eq_matrix_trace d, Algebra.trace_eq_matrix_trace b,
    Quotients.FiniteDescent.InvariantPolynomialOf.Construction.InvariantPolynomial.leftMulMatrix_map_of_basis φ f hf b d hd]
  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

def schemeTrace {X Y : Scheme.{u}} (f : X ⟶ Y) (a : Γ(X, ⊤)) : Γ(Y, ⊤) :=
  letI := f.appTop.hom.toAlgebra
  Algebra.trace Γ(Y, ⊤) Γ(X, ⊤) a

theorem schemeTrace_baseChange
    {X Y X' Y' : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine X'] [IsAffine Y']
    (f : X ⟶ Y) (g : X' ⟶ Y') (j : X' ⟶ X) (i : Y' ⟶ Y)
    (hs : IsPullback j g f i) {ι : Type v} [Fintype ι]
    (b : letI := f.appTop.hom.toAlgebra; Module.Basis ι Γ(Y, ⊤) Γ(X, ⊤))
    (a : Γ(X, ⊤)) : schemeTrace g (j.appTop a) = i.appTop (schemeTrace f a) := by
  obtain ⟨b', hb'⟩ := Quotients.FiniteDescent.AffineGroupoidIs.Construction.AffineGroupoid.exists_basis_of_isPushout
    f.appTop i.appTop j.appTop g.appTop (isPushout_appTop_of_isPullback hs) b
  let := f.appTop.hom.toAlgebra
  let := g.appTop.hom.toAlgebra
  apply trace_map_of_basis i.appTop.hom j.appTop.hom _ b b' hb'
  intro r
  exact congrArg (fun a : X' ⟶ Y => a.appTop r) hs.w

theorem schemeTrace_scalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : Γ(Y, ⊤)) (a : Γ(X, ⊤)) :
    schemeTrace f (f.appTop r * a) = r * schemeTrace f a := by
  let := f.appTop.hom.toAlgebra
  exact (Algebra.trace Γ(Y, ⊤) Γ(X, ⊤)).map_smul r a

theorem schemeTrace_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    {ι : Type v} [Fintype ι]
    (b : letI := f.appTop.hom.toAlgebra; Module.Basis ι Γ(Y, ⊤) Γ(X, ⊤))
    (r : Γ(Y, ⊤)) : schemeTrace f (f.appTop r) = Fintype.card ι • r := by
  let := f.appTop.hom.toAlgebra
  exact Algebra.trace_algebraMap_of_basis b r

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Trace.Construction
