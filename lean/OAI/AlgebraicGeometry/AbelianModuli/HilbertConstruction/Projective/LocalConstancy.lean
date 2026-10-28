import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Specialization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.SpecializationConstancy

/-! # Local Constancy -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A flat projective family's actual fiber Hilbert polynomial is locally constant on a Noetherian base and takes only finitely many values. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} [IsNoetherian S] {n : ℕ}
variable (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver S n))

theorem Closed.Families.FlatClosedFamily.fiberHilbertPolynomial_isLocallyConstant : IsLocallyConstant F.fiberHilbertPolynomial :=
  Noetherian.SpecializationConstancy.noetherian_isLocallyConstant_of_specialization F.fiberHilbertPolynomial
    (fun _ _ h => F.fiberHilbertPolynomial_eq_of_specializes h)

theorem Closed.Families.FlatClosedFamily.fiberHilbertPolynomial_finite_range : (Set.range F.fiberHilbertPolynomial).Finite :=
  F.fiberHilbertPolynomial_isLocallyConstant.range_finite

def Closed.Families.FlatClosedFamily.hilbertPolynomialBaseOpen (P : Polynomial ℚ) : S.Opens :=
  ⟨{s | F.fiberHilbertPolynomial s = P}, F.fiberHilbertPolynomial_isLocallyConstant.isOpen_fiber P⟩

theorem Closed.Families.FlatClosedFamily.hilbertPolynomialBaseOpen_isClosed (P : Polynomial ℚ) :
    IsClosed (F.hilbertPolynomialBaseOpen P : Set S) :=
  F.fiberHilbertPolynomial_isLocallyConstant.isClosed_fiber P

theorem Closed.Families.FlatClosedFamily.hilbertPolynomialBaseOpen_covers :
    iSup (F.hilbertPolynomialBaseOpen) = ⊤ := by
  apply top_unique
  intro s _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨F.fiberHilbertPolynomial s, rfl⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
