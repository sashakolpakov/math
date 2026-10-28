import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.CoordinateBasis

/-! # Degree Index Nonempty -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.DegreeIndexNonempty.GradedHilbert

noncomputable section

/-! Every homogeneous degree has a monomial coordinate, including degree
zero. Hence every finite Plücker coordinate type used here is nonempty. -/

universe u

instance degreeIndex_nonempty (n d : ℕ) : Nonempty (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n d) :=
  ⟨⟨⟨Finsupp.single (0 : Fin (n + 1)) d, Finsupp.degree_single _ _⟩⟩⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.DegreeIndexNonempty.GradedHilbert
