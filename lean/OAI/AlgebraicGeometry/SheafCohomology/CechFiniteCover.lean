import OAI.AlgebraicGeometry.SheafCohomology.CechAcyclicIntersections

/-! # Cech Finite Cover -/

namespace OAI.AlgebraicGeometry.SheafCohomology.CechFiniteCover.Projective

noncomputable section

/-! A finite affine cover of the actual variety and acyclicity of its intersections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

/-- A finite subcover of the actual scheme's affine cover. -/
abbrev finiteAffineCover (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : A.carrier.OpenCover :=
  A.carrier.affineCover.finiteSubcover

instance finiteAffineCover_fintype (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    Fintype (finiteAffineCover A).I₀ := by
  unfold finiteAffineCover
  infer_instance

/-- The image opens in the chosen finite affine cover. -/
def finiteAffineCoverOpen (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (i : (finiteAffineCover A).I₀) :
    A.carrier.Opens :=
  ((finiteAffineCover A).f i).opensRange

theorem finiteAffineCoverOpen_covers (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    IsOpenCover (finiteAffineCoverOpen A) :=
  (finiteAffineCover A).isOpenCover_opensRange

theorem finiteAffineCoverOpen_affine (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (i : (finiteAffineCover A).I₀) : IsAffineOpen (finiteAffineCoverOpen A i) := by
  have : IsAffine ((finiteAffineCover A).X i) := by
    exact isAffine_Spec _
  exact isAffineOpen_opensRange ((finiteAffineCover A).f i)

/-- All intersection cohomology groups vanish in positive degrees for a line bundle. -/
theorem finiteCoverLineBundleIntersectionCohomology_vanish
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : Sheaves.Projective.LineBundle A) (n q : ℕ)
    (i : Fin (n + 1) → (finiteAffineCover A).I₀) :
    Subsingleton (AffineH.Projective.H
      ((Scheme.Modules.restrictFunctor
        (∏ᶜ fun k : Fin (n + 1) => finiteAffineCoverOpen A (i k)).ι).obj L.sheaf)
      (q + 1)) :=
  CechAcyclicIntersections.Projective.lineBundleAffineIntersectionCohomology_vanish A L (finiteAffineCoverOpen A)
    (finiteAffineCoverOpen_affine A) n q i

end

end OAI.AlgebraicGeometry.SheafCohomology.CechFiniteCover.Projective
