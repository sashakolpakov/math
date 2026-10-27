/-
Discussions and model prompting: Alexander Kolpakov (UATX).

Source: sashakolpakov/spherical-regge-scissors, commit
d40eb8990bcf1ba5525435f8517e9ba5c202b549.
-/

import SphericalReggeScissors.ThreeWeight

/-!
# Specialization and return to scissors congruence

The results here are diagram chases.  Every deep comparison or
injectivity theorem appears as a field of an input structure; the proofs
below perform only the internal deductions made in the final section of
the manuscript.
-/

namespace SphericalReggeScissors

universe uU uM uF uQ uQM uK uP uS uR uRQ uG uT uPiece

section Specialization

variable {Universal : Type uU} {Fibre : Type uF}
variable {Middle : Type uM} {Quadric : Type uQ} {QuadricMiddle : Type uQM}
variable {K3 : Type uK}
variable {SphericalPresentation : Type uG}
variable [AddCommGroup Universal] [Module ℚ Universal]
variable [AddCommGroup Middle] [Module ℚ Middle]
variable [AddCommGroup Fibre] [Module ℚ Fibre]
variable [AddCommGroup Quadric] [Module ℚ Quadric]
variable [AddCommGroup QuadricMiddle] [Module ℚ QuadricMiddle]
variable [AddCommGroup K3] [Module ℚ K3]
variable [AddCommGroup SphericalPresentation] [Module ℚ SphericalPresentation]

/--
The specialization/Goncharov diagram chase.

If the relative defect is zero, its specialized endpoint is zero.  Fibre
comparison identifies that endpoint with `c_G` of the dual quadric defect.
Injectivity of `c_G`, projective duality, and the spherical map then forces
the reduced spherical defect to vanish.
-/
theorem goncharov_spherical_defect_vanishes
    (I : SpecializationInputs Universal Middle Fibre Quadric QuadricMiddle K3
      SphericalPresentation)
    (universalDefect : Universal) (quadricDualDefect : Quadric)
    (sphericalDefect : SphericalPresentation)
    (hprimitive : quadricDualDefect ∈ I.quadricCoproduct.ker)
    (huniversal : universalDefect = 0)
    (hfibre :
      I.goncharov ⟨quadricDualDefect, hprimitive⟩ =
        I.endpoint (I.specialize universalDefect))
    (hdual : quadricDualDefect = I.duality (I.spherical sphericalDefect)) :
    sphericalDefect = 0 := by
  have hGoncharov : I.goncharov ⟨quadricDualDefect, hprimitive⟩ = 0 := by
    rw [hfibre, huniversal]
    simp
  have hPrimitive :
      (⟨quadricDualDefect, hprimitive⟩ : I.quadricCoproduct.ker) = 0 := by
    apply I.goncharov_injective
    simpa using hGoncharov
  have hQuadric : quadricDualDefect = 0 :=
    congrArg Subtype.val hPrimitive
  have hDualSpherical : I.duality (I.spherical sphericalDefect) = 0 := by
    rw [← hdual, hQuadric]
  have hSpherical : I.spherical sphericalDefect = 0 := by
    apply I.duality_involutive.injective
    simpa using hDualSpherical
  apply I.spherical_injective
  simpa using hSpherical

end Specialization

section Suspension

variable {Plane : Type uP} {Full : Type uS} {Reduced : Type uR}
variable {ReducedRational : Type uRQ}
variable {SphericalPresentation : Type uG}
variable {Tetrahedron : Type uT}
variable {Piece : Type uPiece}
variable [AddCommGroup Plane] [AddCommGroup Full] [AddCommGroup Reduced]
variable [AddCommGroup ReducedRational] [Module ℚ ReducedRational]
variable [AddCommGroup SphericalPresentation] [Module ℚ SphericalPresentation]

/-- E7 is used here as an actual isomorphism, not as a silent
identification of the two spherical presentations. -/
theorem reduced_rational_defect_vanishes_of_presentation
    (comparison : ReducedRational ≃ₗ[ℚ] SphericalPresentation)
    (reducedRationalDefect : ReducedRational)
    (sphericalPresentationDefect : SphericalPresentation)
    (hspherical : sphericalPresentationDefect = 0)
    (hcomparison :
      sphericalPresentationDefect = comparison reducedRationalDefect) :
    reducedRationalDefect = 0 := by
  apply comparison.injective
  rw [← hcomparison, hspherical]
  simp

/-- Vanishing after tensoring with `ℚ` descends to the integral reduced
scissors group because that rationalization map is injective.  In the
manuscript this injectivity follows from unique divisibility. -/
theorem integral_reduced_defect_vanishes
    (I : ScissorsInputs Plane Full Reduced ReducedRational Tetrahedron Piece)
    (reducedDefect : Reduced) (reducedRationalDefect : ReducedRational)
    (hrational : reducedRationalDefect = 0)
    (hcomparison : reducedRationalDefect = I.rationalize reducedDefect) :
    reducedDefect = 0 := by
  apply I.rationalization_injective
  rw [← hcomparison, hrational]
  simp

/--
The reduced-to-full argument using suspension, volume, and area.

This is the precise algebraic content of the manuscript's last paragraph:
zero after reduction makes the full defect a suspension; equal volume and
`Vol (Σq) = (π/2) Area(q)` give zero area; area classification then kills
the suspended class.
-/
theorem full_defect_vanishes
    (I : ScissorsInputs Plane Full Reduced ReducedRational Tetrahedron Piece)
    (z : Full)
    (hreduced : I.reduction z = 0)
    (hvolume : I.volume z = 0) : z = 0 := by
  obtain ⟨q, hq⟩ := I.exact_at_full z hreduced
  have hProduct : (Real.pi / 2) * I.area q = 0 := by
    calc
      (Real.pi / 2) * I.area q = I.volume (I.suspension q) :=
        (I.suspension_volume q).symm
      _ = I.volume z := congrArg I.volume hq
      _ = 0 := hvolume
  have hScale : (Real.pi / 2 : ℝ) ≠ 0 := by
    exact div_ne_zero Real.pi_ne_zero (by norm_num)
  have hArea : I.area q = 0 := (mul_eq_zero.mp hProduct).resolve_left hScale
  have hqZero : q = 0 := by
    apply I.area_injective
    simpa using hArea
  rw [← hq, hqZero]
  simp

/-- Equal volumes make the volume of the additive Regge defect zero. -/
theorem volume_defect_vanishes
    (I : ScissorsInputs Plane Full Reduced ReducedRational Tetrahedron Piece)
    {x y : Tetrahedron}
    (hvolume : I.volume (I.scissorsClass x) = I.volume (I.scissorsClass y)) :
    I.volume (I.scissorsClass x - I.scissorsClass y) = 0 := by
  simpa [map_sub] using sub_eq_zero.mpr hvolume

/-- Equality of the full additive defect gives equality of scissors
classes and hence, by the supplied cancellation theorem, a concrete
finite-equidecomposition certificate. -/
theorem equidecomposable_of_full_defect_zero
    (I : ScissorsInputs Plane Full Reduced ReducedRational Tetrahedron Piece)
    {x y : Tetrahedron}
    (hdefect : I.scissorsClass x - I.scissorsClass y = 0) :
    Nonempty (FiniteEquidecomposition Tetrahedron Piece
      I.decomposes I.pieceIsometric x y) := by
  apply I.cancellation
  exact sub_eq_zero.mp hdefect

end Suspension

end SphericalReggeScissors
