import OAI.AlgebraicGeometry.Comparison.Betti.Projective.FrameCoefficients
import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.LaurentEvaluation

/-! # Cech Frame Transport -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechFrameTransport.Dolbeault

noncomputable section

section

/-! Frame coefficients commute with the exact open transport in the original algebraic Cech map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

open _root_.MvPolynomial

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveAlgebraicCechSectionIso_hom_map (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (t : Fin (q + 1) → Fin (n + 1))
    (m : (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).val.presheaf.obj
      (op (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := ℂ) (fun k => ULift.up (t k))))) :
    (ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveAlgebraicCechSectionIso n j d q t).hom m =
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).val.presheaf.map
        (homOfLE (IntersectionLaurentCoordinates.Dolbeault.projectiveCechAlgebraicOpen_eq n q t).ge).op m :=
  ConcreteCategory.congr_hom
    (congrArg (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).val.presheaf.map (Subsingleton.elim _ _)) m

theorem projectiveAlgebraicTwistCechFrameCoefficient_transport (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (z : (ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveAlgebraicTwistCechComplex n j d).X q) (t : Fin (q + 1) → Fin (n + 1)) :
    ProjectiveTwist.CechConeEvaluation.Dolbeault.projectiveAlgebraicTwistCechFrameCoefficient n j d q z t =
      (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).presheaf.map (homOfLE (IntersectionLaurentCoordinates.Dolbeault.projectiveCechAlgebraicOpen_eq n q t).ge).op
        (FrameCoefficients.Dolbeault.projectiveAlgebraicTwistOpenCoefficient n
          (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := ℂ) (fun k => ULift.up (t k))) (t 0)
          (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := ℂ) (fun k => ULift.up (t k)) 0) j d
          (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).val.presheaf
            (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n) q z t)) := by
  let M := SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d
  let m := SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv M.val.presheaf (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n) q z t
  let V := Intersections.Dolbeault.projectiveAlgebraicIntersection n (Finset.univ.image t)
  let hi := Intersections.Dolbeault.projectiveAlgebraicIntersection_le n (Finset.univ.image t) (t 0)
    (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)
  have hm := projectiveAlgebraicCechSectionIso_hom_map n j d q t m
  have hc := congrArg (FrameCoefficients.Dolbeault.projectiveAlgebraicTwistOpenCoefficient n V (t 0) hi j d) hm
  exact hc.trans (FrameCoefficients.Dolbeault.projectiveAlgebraicTwistOpenCoefficient_restrict n
    (IntersectionLaurentCoordinates.Dolbeault.projectiveCechAlgebraicOpen_eq n q t).ge (t 0)
    (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := ℂ) (fun k => ULift.up (t k)) 0) j d m)

end

/-! The Laurent coefficients used to evaluate the actual comparison are the existing original base-Cech coefficients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

open _root_.MvPolynomial

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveAlgebraicIntersection_section_roundtrip (n q : ℕ) (t : Fin (q + 1) → Fin (n + 1))
    (s : Γ(Foundations.Scheme.ProjectiveSpace.projectiveSpace n, SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := ℂ) (fun k => ULift.up (t k)))) :
    (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).presheaf.map (homOfLE (IntersectionLaurentCoordinates.Dolbeault.projectiveCechAlgebraicOpen_eq n q t).le).op
      ((Foundations.Scheme.ProjectiveSpace.projectiveSpace n).presheaf.map (homOfLE (IntersectionLaurentCoordinates.Dolbeault.projectiveCechAlgebraicOpen_eq n q t).ge).op s) = s := by
  let F := (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).presheaf
  let f := (homOfLE (IntersectionLaurentCoordinates.Dolbeault.projectiveCechAlgebraicOpen_eq n q t).ge).op
  let g := (homOfLE (IntersectionLaurentCoordinates.Dolbeault.projectiveCechAlgebraicOpen_eq n q t).le).op
  have h : F.map f ≫ F.map g = 𝟙 _ :=
    (F.map_comp f g).symm.trans
      ((congrArg F.map (Subsingleton.elim (f ≫ g) (𝟙 _))).trans (F.map_id _))
  exact ConcreteCategory.congr_hom h s

def projectiveAlgebraicCechBaseFactor (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (z : (ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveAlgebraicTwistCechComplex n j d).X q) (t : Fin (q + 1) → Fin (n + 1)) :
    SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := Fin (n + 1)))
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d) (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := ℂ)) q
      (fun k => ULift.up (t k)) :=
  SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).val.presheaf (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n) q z t

theorem projectiveAlgebraicTwistCechLaurentCoordinates_baseFactor (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (z : (ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveAlgebraicTwistCechComplex n j d).X q) (t : Fin (q + 1) → Fin (n + 1)) :
    ProjectiveTwist.LaurentEvaluation.Dolbeault.projectiveAlgebraicTwistCechLaurentCoordinates n j d q z t =
      SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionLaurentRingEquiv (R := ℂ) (fun k => ULift.up (t k))
        ((SheafCohomology.Projective.TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := ℂ) (fun k => ULift.up (t k)) j d).hom
          (projectiveAlgebraicCechBaseFactor n j d q z t)) := by
  let E := SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionLaurentRingEquiv (R := ℂ) (fun k => ULift.up (t k))
  let m := projectiveAlgebraicCechBaseFactor n j d q z t
  let c := FrameCoefficients.Dolbeault.projectiveAlgebraicTwistOpenCoefficient n
    (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := ℂ) (fun k => ULift.up (t k))) (t 0)
    (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := ℂ) (fun k => ULift.up (t k)) 0) j d m
  have ht := IntersectionLaurentCoordinates.Dolbeault.projectiveIntersectionLaurentCoordinates_restrict n q t
    (ProjectiveTwist.CechConeEvaluation.Dolbeault.projectiveAlgebraicTwistCechFrameCoefficient n j d q z t)
  have hf := projectiveAlgebraicTwistCechFrameCoefficient_transport n j d q z t
  have hc := congrArg (fun s => E ((Foundations.Scheme.ProjectiveSpace.projectiveSpace n).presheaf.map
    (homOfLE (IntersectionLaurentCoordinates.Dolbeault.projectiveCechAlgebraicOpen_eq n q t).le).op s)) hf
  have hr := congrArg E (projectiveAlgebraicIntersection_section_roundtrip n q t c)
  have hb := congrArg E (FrameCoefficients.Dolbeault.projectiveTwistBaseFactor_coefficient n j d q (fun k => ULift.up (t k)) m)
  exact ht.trans (hc.trans (hr.trans hb.symm))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechFrameTransport.Dolbeault
