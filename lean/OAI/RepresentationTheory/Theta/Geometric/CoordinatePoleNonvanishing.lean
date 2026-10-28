import OAI.RepresentationTheory.Theta.Geometric.SectionFrameNonvanishing

/-! # Coordinate Pole Nonvanishing -/

namespace OAI.RepresentationTheory.Theta.Geometric.CoordinatePoleNonvanishing

noncomputable section

/-! The actual coordinate section of the hyperplane dual is nonvanishing
exactly on its standard projective chart. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem coordinatePoleSection_nonvanishing (n : ℕ) (j : Fin (n + 1)) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AlgebraicGeometry.SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleUnitHom (R := ℂ) j) =
      AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) j := by
  let X := AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n
  let U : Fin (n + 1) → X.Opens := fun i => AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) i
  have hU : iSup U = ⊤ := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top
  ext x
  have hx : x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have h := SectionFrameNonvanishing.sectionNonvanishing_in_frame (AlgebraicGeometry.SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleUnitHom (R := ℂ) j)
    ⟨U i, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩
    (AlgebraicGeometry.SheafCohomology.Projective.HyperplaneFrames.MvPolynomial.coordinateHyperplanePoleSheafTrivialization (R := ℂ) i j)
  have hc := AlgebraicGeometry.SheafCohomology.Projective.HyperplaneLocalSection.MvPolynomial.coordinateHyperplanePoleSection_localTrivializationTopSection (R := ℂ) i j
  have hc' := congrArg (U i).toScheme.basicOpen hc
  have h' := h.trans hc'
  rw [AlgebraicGeometry.SheafCohomology.Projective.FrameSections.affineOpenTopSection_eq_topIso_inv] at h'
  have hh := congrArg (fun V => (U i).ι ''ᵁ V) h'
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.ι_image_basicOpen_topIso_inv,
    AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_basicOpen,
    AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_eq] at hh
  have hx' := (congrArg (fun V : X.Opens => x ∈ V) hh).to_iff
  simpa [U, hi] using hx'

end

end OAI.RepresentationTheory.Theta.Geometric.CoordinatePoleNonvanishing
