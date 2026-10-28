import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismOpenCoverRigidity
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.TestBaseCover

/-! # Open Polarized Rigidity -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.OpenPolarizedRigidity

noncomputable section

/-! Multiply the finitely many localization coefficients from an open
cover. Actual automorphism equality then glues over every reduced test. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem finite_open_polarized_rigidity_away
    {R : Type} [CommRing R] [IsDomain R] {S : Scheme.{0}} (p : S ⟶ Spec (.of R))
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    {I : Type} [Fintype I] (U : I → S.Opens) (hU : iSup U = ⊤)
    (r : I → R) (hr : ∀ i, r i ≠ 0)
    (hlocal : ∀ i, ∀ (T : Over S) [IsReduced T.left]
      (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (A.pullback T.hom)),
      (∀ x : T.left, T.hom x ∈ U i) →
      (∀ x : T.left, r i ∉ (p (T.hom x)).asIdeal) →
      e.abelian.hom = 𝟙 (A.abelian.pullback T.hom).scheme) :
    ∃ a : R, a ≠ 0 ∧ ∀ (T : Over S) [IsReduced T.left]
      (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (A.pullback T.hom)),
      (∀ x : T.left, a ∉ (p (T.hom x)).asIdeal) →
      e.abelian.hom = 𝟙 (A.abelian.pullback T.hom).scheme := by
  classical
  refine ⟨∏ i, r i, Finset.prod_ne_zero_iff.mpr (fun i _ => hr i), ?_⟩
  intro T _ e hunit
  let C := Reduced.TestBaseCover.testBaseOpenCover U hU T
  apply Polarized.AutomorphismOpenCoverRigidity.polarized_automorphism_eq_id_of_open_cover A T C e
  intro i
  change I at i
  let V := OverOpenCoverGluing.OverOpenCover.obj T C i
  let j := OverOpenCoverGluing.OverOpenCover.inclusion T C i
  apply hlocal i V (Polarized.AutomorphismRestriction.restrictPolarizedAutomorphism A j e) (Reduced.TestBaseCover.testBaseOpenCover_mapsTo U hU T i)
  intro x hbad
  have hx : p (V.hom x) = p (T.hom (j.left x)) :=
    congrArg p (congrArg (fun q : V.left ⟶ S => q x) j.w).symm
  have hmem : (∏ k, r k) ∈ (p (T.hom (j.left x))).asIdeal := by
    rw [← hx]
    exact (p (V.hom x)).asIdeal.mem_of_dvd
      (Finset.dvd_prod_of_mem r (Finset.mem_univ i)) hbad
  exact hunit (j.left x) hmem

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.OpenPolarizedRigidity
