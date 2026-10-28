import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ProjectiveCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.FamilyBaseChange

/-! # Fiber Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual residue-field Hilbert polynomial of a flat projective family determines its Hilbert polynomial at every field-valued point. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} {n : ℕ} (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver S n))

def Closed.Families.FlatClosedFamily.fiberHilbertPolynomial (x : S) : Polynomial ℚ :=
  (HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert.exists_hilbertPolynomial (F.affineProjectivePullback (S.fromSpecResidueField x)).homogeneousIdeal).choose

theorem Closed.Families.FlatClosedFamily.fiberHilbertPolynomial_spec (x : S) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (F.affineProjectivePullback (S.fromSpecResidueField x)).homogeneousIdeal.toIdeal
      (F.fiberHilbertPolynomial x) :=
  (HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert.exists_hilbertPolynomial (F.affineProjectivePullback (S.fromSpecResidueField x)).homogeneousIdeal).choose_spec

theorem Closed.Families.FlatClosedFamily.fieldPoint_fiberHilbertPolynomial {K : Type u} [Field K] (s : Spec (.of K) ⟶ S) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (F.affineProjectivePullback s).homogeneousIdeal.toIdeal
      (F.fiberHilbertPolynomial (s (IsLocalRing.closedPoint K))) := by
  let x := s (IsLocalRing.closedPoint K)
  let φ : S.residueField x ⟶ CommRingCat.of K := S.descResidueField (Scheme.stalkClosedPointTo s)
  have hφ : Spec.map φ ≫ S.fromSpecResidueField x = s :=
    S.descResidueField_stalkClosedPointTo_fromSpecResidueField K s
  have he := (congrArg (fun b => F.affineProjectivePullback b) hφ).symm.trans
    (F.affineProjectivePullback_coefficient (S.fromSpecResidueField x) φ)
  rw [he]
  exact ((F.affineProjectivePullback (S.fromSpecResidueField x)).coefficientField_hilbertPolynomial_iff
    φ (F.fiberHilbertPolynomial x)).mpr (F.fiberHilbertPolynomial_spec x)

theorem Closed.Families.FlatClosedFamily.fieldPoint_hilbertPolynomial_iff {K : Type u} [Field K] (s : Spec (.of K) ⟶ S)
    (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (F.affineProjectivePullback s).homogeneousIdeal.toIdeal P ↔
      F.fiberHilbertPolynomial (s (IsLocalRing.closedPoint K)) = P := by
  constructor
  · intro h
    exact HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertPolynomial_unique (F.fieldPoint_fiberHilbertPolynomial s) h
  · intro h
    exact h ▸ F.fieldPoint_fiberHilbertPolynomial s

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
