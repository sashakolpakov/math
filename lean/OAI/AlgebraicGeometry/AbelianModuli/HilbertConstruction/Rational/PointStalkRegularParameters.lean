import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FieldEtaleCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.StalkScalarResidue
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.RationalRetractionParameters
import Mathlib.RingTheory.Smooth.Flat

/-! # Point Stalk Regular Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PointStalkRegularParameters

noncomputable section

/-! The actual stalk at a rational point of a smooth g-dimensional field scheme admits a regular sequence of g generators for its maximal ideal. The affine etale chart, rational retraction, and regular sequence are all constructed from the geometric input. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry IsLocalRing
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem rationalPoint_stalk_regular_parameters
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (g : ℕ) [SmoothOfRelativeDimension g p]
    (s : Spec (.of K) ⟶ X) (hs : s ≫ p = 𝟙 _) :
    ∃ rs : List (X.presheaf.stalk (s (IsLocalRing.closedPoint K))),
      Regular.SequenceBasic.RingTheory.Sequence.IsRegular (X.presheaf.stalk (s (IsLocalRing.closedPoint K))) rs ∧
      Regular.SequenceBasic.Ideal.ofList rs = maximalIdeal (X.presheaf.stalk (s (IsLocalRing.closedPoint K))) ∧
      rs.length = g := by
  let x := s (IsLocalRing.closedPoint K)
  obtain ⟨V, hV, hx, ι, hι, φ, hcard, het, hcoeff⟩ :=
    HilbertConstruction.Smooth.FieldEtaleCoordinates.smoothField_exists_affine_etale_coordinates p g x
  let : Finite ι := hι
  let P := MvPolynomial ι K
  let A := Γ(X, V)
  let O := X.presheaf.stalk x
  let r : A →+* O := (X.presheaf.germ V x hx).hom
  let : Algebra P A := φ.toAlgebra
  let : Algebra A O := r.toAlgebra
  let : Algebra P O := (r.comp φ).toAlgebra
  let : IsScalarTower P A O := IsScalarTower.of_algebraMap_eq' rfl
  let M := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  have : IsLocalization M O := hV.isLocalization_stalk ⟨x, hx⟩
  have : Algebra.Etale P A := het
  have : Module.Flat P A := inferInstance
  have : Module.Flat A O := IsLocalization.flat O M
  have : Module.Flat P O := Module.Flat.trans P A O
  have : Algebra.EssFiniteType A O := Algebra.EssFiniteType.of_isLocalization O M
  have : Algebra.EssFiniteType P O := Algebra.EssFiniteType.comp P A O
  have : Algebra.FormallyUnramified A O := Algebra.FormallyUnramified.of_isLocalization M
  have : Algebra.FormallyUnramified P O := Algebra.FormallyUnramified.comp P A O
  let e := PointResidue.rationalPointResidueIso p s hs
  let ε : O →+* K := (X.residue x ≫ e.hom).hom
  have hsplit : (ε.comp (algebraMap P O)).comp MvPolynomial.C = RingHom.id K := by
    ext k
    change e.hom (X.residue x (X.presheaf.germ V x hx (φ (MvPolynomial.C k)))) = k
    rw [show φ (MvPolynomial.C k) =
      X.presheaf.map V.leTop.op (p.appTop ((Scheme.ΓSpecIso (.of K)).inv k)) from
        RingHom.congr_fun hcoeff k]
    rw [X.presheaf.germ_res_apply V.leTop x hx]
    have h := congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of K => f k)
      (StalkScalarResidue.rationalStalkResidueCoefficient_comp_residueIso p s hs)
    exact h
  obtain ⟨rs, hreg, hgen, hlen⟩ :=
    Polynomial.RationalRetractionParameters.polynomial_flat_unramified_retraction_regular_parameters O ε hsplit
  exact ⟨rs, hreg, hgen, hlen.trans hcard⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PointStalkRegularParameters
