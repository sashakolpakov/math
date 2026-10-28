import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.GeometricRigidity
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothEquationSupport
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.NoetherianGenericClosedLocus

/-! # Generic Polarized Automorphism Support -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.GenericPolarizedAutomorphismSupport

noncomputable section

/-! Characteristic-zero rigidity forces the nonidentity locus of an
actual universal polarized automorphism to be vertical. Noetherianity
then removes that locus by one nonzero equation on the coefficient base. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {R K : Type} [CommRing R] [Field K] [CharZero K] [Countable K]
    (ι : R →+* K) (hι : Function.Injective ι)
    {Z : Scheme.{0}} (p : Z ⟶ Spec (.of R)) [LocallyOfFiniteType p]
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Z)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A A) (hN : 3 ≤ N)

include ι hι hN

theorem generic_polarized_automorphism_support (z : Z) (hz : (p z).asIdeal = ⊥) :
    z ∈ SmoothEquationSupport.smoothEquationSupport e.abelian.hom (𝟙 A.abelian.scheme) := by
  let b : Spec (.of K) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom ι)
  have hb : p z ∈ Set.range b := by
    refine ⟨(⊥ : PrimeSpectrum K), PrimeSpectrum.ext ?_⟩
    exact (Ideal.comap_bot_of_injective ι hι).trans hz.symm
  have hpoint : z ∈ Set.range (pullback.fst p b) := by
    rw [Scheme.Pullback.range_fst]
    exact hb
  obtain ⟨y, hy⟩ := hpoint
  let F := AlgebraicClosure ((pullback p b).residueField y)
  let q : Spec (.of F) ⟶ pullback p b :=
    Spec.map (CommRingCat.ofHom (algebraMap ((pullback p b).residueField y) F)) ≫
      (pullback p b).fromSpecResidueField y
  have hq : q (default : Spec (.of F)) = y := (pullback p b).fromSpecResidueField_apply y _
  let a := q ≫ pullback.fst p b
  have ha : a (default : Spec (.of F)) = z := (congrArg (pullback.fst p b) hq).trans hy
  have he : (e.pullback a).abelian.hom = 𝟙 (A.abelian.pullback a).scheme := by
    apply AbelianModuli.ReferenceFamily.Pure.AutomorphismDescent.pure_abelian_eq_id_via (e.pullback a)
      (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A (pullback.fst p b) q).symm
    intro u
    exact AbelianModuli.ReferenceFamily.Pure.GeometricRigidity.pureGeometricPullback_abelian_eq_id (pullback.snd p b)
      (A.pullback (pullback.fst p b)) hN q u
  have heq : (Over.pullback a).map e.abelian.hom = (Over.pullback a).map (𝟙 A.abelian.scheme) :=
    he.trans ((Over.pullback a).map_id A.abelian.scheme).symm
  exact SmoothEquationSupport.equation_range_subset_support e.abelian.hom (𝟙 A.abelian.scheme) a heq ⟨default, ha⟩

theorem polarized_automorphism_identity_away [IsDomain R] [IsNoetherian Z] :
    ∃ r : R, r ≠ 0 ∧ ∀ z : Z, r ∉ (p z).asIdeal →
      z ∈ SmoothEquationSupport.smoothEquationSupport e.abelian.hom (𝟙 A.abelian.scheme) :=
  NoetherianGenericClosedLocus.noetherian_generic_closed_locus_away p _
    (SmoothEquationSupport.smoothEquationSupport_closed e.abelian.hom (𝟙 A.abelian.scheme))
    (generic_polarized_automorphism_support ι hι p A e hN)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.GenericPolarizedAutomorphismSupport
