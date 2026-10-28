import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CanonicalFiberPolynomial
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiberPolynomialLocality
import Mathlib.Topology.Irreducible

/-! # Hilbert Polynomial Agreement -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.HilbertPolynomialAgreement

noncomputable section

/-! Actual canonical fiber polynomials agree on nonempty overlaps.
Over an irreducible test scheme, their local existence gives one global
fiber polynomial, with no polynomial constancy premise. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.CanonicalFiberPolynomial.GradedHilbert

theorem canonicalFiberPolynomial_unique
    {S : Scheme.{0}} {n : ℕ} {T : Over S} [Nonempty T.left]
    (F : HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T) {P Q : Polynomial ℚ}
    (hP : HilbertScheme.Presentations.CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial F P) (hQ : HilbertScheme.Presentations.CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial F Q) : P = Q := by
  let x : T.left := Classical.choice inferInstance
  exact HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertPolynomial_unique (hP (T.left.residueField x) (T.left.fromSpecResidueField x))
    (hQ (T.left.residueField x) (T.left.fromSpecResidueField x))

theorem open_overlap_nonempty
    {S : Scheme.{0}} {U V T : Over S} [PreirreducibleSpace T.left]
    [Nonempty U.left] [Nonempty V.left] (f : U ⟶ T) (g : V ⟶ T)
    [IsOpenImmersion f.left] [IsOpenImmersion g.left] : Nonempty (pullback f g).left := by
  obtain ⟨x, ⟨a, ha⟩, ⟨b, hb⟩⟩ := nonempty_preirreducible_inter
    f.left.isOpenEmbedding.isOpenMap.isOpen_range g.left.isOpenEmbedding.isOpenMap.isOpen_range
    (Set.range_nonempty f.left) (Set.range_nonempty g.left)
  obtain ⟨z, _, _⟩ := Scheme.exists_preimage_of_isPullback
    ((IsPullback.of_hasPullback f g).map (Over.forget S)) a b (ha.trans hb.symm)
  exact ⟨z⟩

theorem canonicalFiberPolynomial_open_agreement
    {S : Scheme.{0}} {n : ℕ} {U V T : Over S} [PreirreducibleSpace T.left]
    [Nonempty U.left] [Nonempty V.left] (f : U ⟶ T) (g : V ⟶ T)
    [IsOpenImmersion f.left] [IsOpenImmersion g.left]
    (F : HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T) {P Q : Polynomial ℚ}
    (hP : HilbertScheme.Presentations.CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily _ f F) P)
    (hQ : HilbertScheme.Presentations.CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily _ g F) Q) : P = Q := by
  have : Nonempty (pullback f g).left := open_overlap_nonempty f g
  have hp := hP.pullback (pullback.fst f g)
  have hq := hQ.pullback (pullback.snd f g)
  rw [← HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily_comp] at hp hq
  rw [pullback.condition] at hp
  exact canonicalFiberPolynomial_unique _ hp hq

theorem exists_fiberPolynomial_of_irreducible_open_cover
    {S : Scheme.{0}} {n : ℕ} {T : Over S} [IrreducibleSpace T.left]
    {ι : Type} (U : ι → Over S) (f : ∀ i, U i ⟶ T)
    [∀ i, Nonempty (U i).left] [∀ i, IsOpenImmersion (f i).left]
    (hcover : ∀ t : T.left, ∃ i, ∃ y : (U i).left, (f i).left y = t)
    (F : HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T)
    (hlocal : ∀ i, ∃ P : Polynomial ℚ, HilbertScheme.Presentations.CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily _ (f i) F) P) :
    ∃ P : Polynomial ℚ, HilbertScheme.Presentations.Has.Core.HasFiberHilbertPolynomial (HilbertScheme.Presentations.Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S n) F P := by
  choose P hP using hlocal
  obtain ⟨i₀, _, _⟩ := hcover (Classical.choice (inferInstance : Nonempty T.left))
  refine ⟨P i₀, HilbertScheme.Presentations.FiberPolynomialLocality.Core.hasFiberHilbertPolynomial_of_openCover
    (HilbertScheme.Presentations.Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S n) U f hcover F (P i₀) ?_⟩
  intro i
  have he := canonicalFiberPolynomial_open_agreement (f i) (f i₀) F (hP i) (hP i₀)
  exact he ▸ (hP i).hasFiberHilbertPolynomial

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.HilbertPolynomialAgreement
