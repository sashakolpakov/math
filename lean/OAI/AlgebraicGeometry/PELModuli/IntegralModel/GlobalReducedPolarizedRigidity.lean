import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.ReducedPolarizedRigidity
import OAI.ArithmeticGeometry.Models.SpreadingOut.FiniteAffineCover

/-! # Global Reduced Polarized Rigidity -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.GlobalReducedPolarizedRigidity

noncomputable section

/-! Arithmetic full-level rigidity on all reduced tests of an arbitrary
noetherian finite-type polarized family. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem polarized_reduced_rigidity_away
    {R K : Type} [CommRing R] [IsDomain R] [Field K] [CharZero K] [Countable K]
    (ι : R →+* K) (hι : Function.Injective ι)
    {S : Scheme.{0}} [IsNoetherian S]
    (p : S ⟶ Spec (.of R)) [LocallyOfFiniteType p]
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (hN : 3 ≤ N) (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0}) :
    ∃ r : R, r ≠ 0 ∧ ∀ (T : Over S) [IsReduced T.left]
      (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (A.pullback T.hom)),
      (∀ x : T.left, r ∉ (p (T.hom x)).asIdeal) →
      e.abelian.hom = 𝟙 (A.abelian.pullback T.hom).scheme := by
  classical
  obtain ⟨I, hI, U, hU, hcover⟩ := ArithmeticGeometry.Models.SpreadingOut.FiniteAffineCover.Construction.finite_nonempty_affine_open_cover S
  let := hI
  let : Fintype I := Fintype.ofFinite I
  have ha (i : I) : IsAffine (U i).toScheme := (hU i).1
  have hp (i : I) : LocallyOfFiniteType ((U i).ι ≫ p) := inferInstance
  choose r hr hrigid using fun i : I => Affine.ReducedPolarizedRigidity.affine_polarized_reduced_rigidity_away ι hι
    ((U i).ι ≫ p) (A.pullback (U i).ι) hN hPresentations
  apply Finite.OpenPolarizedRigidity.finite_open_polarized_rigidity_away p A U hcover r hr
  intro i T _ e hT hunit
  let q := Open.BaseFunctorRepresentation.OpenBaseTest.lift (U i) T hT
  have hq : q ≫ (U i).ι = T.hom := Open.BaseFunctorRepresentation.OpenBaseTest.lift_ι (U i) T hT
  apply AbelianModuli.ReferenceFamily.Pure.AutomorphismDescent.pure_abelian_eq_id_via e (AbelianModuli.ReferenceFamily.Pure.AutomorphismDescent.purePullbackFactor A q (U i).ι T.hom hq)
  intro a
  have : IsReduced (Over.mk q).left := inferInstanceAs (IsReduced T.left)
  apply hrigid i (Over.mk q) a
  intro x
  have hx : ((U i).ι ≫ p) (q x) = p (T.hom x) :=
    congrArg p (congrArg (fun f : T.left ⟶ S => f x) hq)
  exact hx.symm ▸ hunit x

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.GlobalReducedPolarizedRigidity
