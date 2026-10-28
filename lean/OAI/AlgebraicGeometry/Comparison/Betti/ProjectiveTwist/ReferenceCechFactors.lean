import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.ReferenceCechMap
import OAI.AlgebraicGeometry.Comparison.Betti.Cech.ProjectionTransport

/-! # Reference Cech Factors -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.ReferenceCechFactors.Dolbeault

noncomputable section

section

/-! Each original projective Čech comparison component is the unit and the two actual open transports. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

open OAI.AlgebraicGeometry.Comparison.Betti.Cech.ProjectionTransport

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def projectiveTwistCoverSectionMap (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (t : Fin (q + 1) → Fin (n + 1)) :
    (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.obj (op (∏ᶜ fun k : Fin (q + 1) =>
      Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n (t k)))) ⟶
    (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.obj (op (∏ᶜ fun k : Fin (q + 1) =>
      Projective.Intersections.Dolbeault.projectiveStandardCover n (t k))) :=
  (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.map (eqToHom (congrArg op
    (congrArg (fun U : Fin (n + 1) → Opens (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n) =>
      ∏ᶜ fun k : Fin (q + 1) => U (t k)) (ReferenceCechMap.Dolbeault.projectiveAnalyticCoverEq n))))

theorem projectiveTwistNativeCoverIso_hom_proj (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (t : Fin (q + 1) → Fin (n + 1)) :
    (ReferenceCechMap.Dolbeault.projectiveTwistNativeCoverIso n j d).hom.f q ≫
        Pi.π (fun a : Fin (q + 1) → Fin (n + 1) => (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.obj
          (op (∏ᶜ fun k => Projective.Intersections.Dolbeault.projectiveStandardCover n (a k)))) t =
      Pi.π (fun a : Fin (q + 1) → Fin (n + 1) => (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.obj
        (op (∏ᶜ fun k => Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n (a k))))) t ≫
          projectiveTwistCoverSectionMap n j d q t :=
  AdditiveCechCoverCongr.additiveCechCoverCongrIso_hom_proj (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj (ReferenceCechMap.Dolbeault.projectiveAnalyticCoverEq n) q t

theorem projectiveTwistOriginalCechMap_proj (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (t : Fin (q + 1) → Fin (n + 1)) :
    (ReferenceCechMap.Dolbeault.projectiveTwistOriginalCechMap n j d).f q ≫
        Pi.π (fun a : Fin (q + 1) → Fin (n + 1) => (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.obj
          (op (∏ᶜ fun k => Projective.Intersections.Dolbeault.projectiveStandardCover n (a k)))) t =
      Pi.π (fun a : Fin (q + 1) → Fin (n + 1) =>
        (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).val.presheaf.obj
          (op (∏ᶜ fun k => Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n (a k)))) t ≫
        (Module.AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
          (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d)).app
            (op (∏ᶜ fun k => Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n (t k))) ≫
          (AdditiveCechImage.additiveCechDirectImageSectionIso (Analytification.Base.analytificationMap (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)))
            (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n) (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj q t).hom ≫
              projectiveTwistCoverSectionMap n j d q t := by
  let p := Pi.π (fun a : Fin (q + 1) → Fin (n + 1) =>
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).val.presheaf.obj
      (op (∏ᶜ fun k => Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n (a k)))) t
  have h := Cech.ProjectionTransport.comp_projection_transport
    ((Module.AnalytificationCechMap.moduleAnalytificationCechMap (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n)).f q)
    ((ReferenceCechMap.Dolbeault.projectiveTwistNativeCoverIso n j d).hom.f q) _ _ (projectiveTwistCoverSectionMap n j d q t) p _
      (projectiveTwistNativeCoverIso_hom_proj n j d q t)
      (Module.AnalytificationCechMap.moduleAnalytificationCechMap_proj (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
        (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n) q t)
  exact h.trans (congrArg (p ≫ ·) (Category.assoc _ _ _))

end

/-! The original projective Čech comparison, transported to actual intersections, is exactly the section unit. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

open OAI.AlgebraicGeometry.Comparison.Betti.Cech.ProjectionTransport

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveTwistOriginalCechMap_factor (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (t : Fin (q + 1) → Fin (n + 1)) :
    (ReferenceCechMap.Dolbeault.projectiveTwistOriginalCechMap n j d).f q ≫
        Pi.π (fun a : Fin (q + 1) → Fin (n + 1) => (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.obj
          (op (∏ᶜ fun k => Projective.Intersections.Dolbeault.projectiveStandardCover n (a k)))) t ≫
            (Projective.CechSectionTransport.Dolbeault.projectiveCechOpenSectionIso n j d q t).hom =
      Pi.π (fun a : Fin (q + 1) → Fin (n + 1) =>
        (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).val.presheaf.obj
          (op (∏ᶜ fun k => Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n (a k)))) t ≫
        (ReferenceCechMap.Dolbeault.projectiveAlgebraicCechSectionIso n j d q t).hom ≫
          (Module.AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
            (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d)).app
              (op (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n (Finset.univ.image t))) := by
  let X := Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  let P := (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).val.presheaf
  let Q := (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj
  let α := Module.AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit X (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d)
  let A : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Opens := ∏ᶜ fun k : Fin (q + 1) => Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n (t k)
  let B := Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n (Finset.univ.image t)
  let g : op A ⟶ op B := eqToHom (congrArg op (ReferenceCechMap.Dolbeault.projectiveAlgebraicCechIntersection_eq n q t))
  let u := α.app (op A)
  let e := (AdditiveCechImage.additiveCechDirectImageSectionIso (Analytification.Base.analytificationMap X) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n) Q q t).hom
  let r := projectiveTwistCoverSectionMap n j d q t
  let v := (Projective.CechSectionTransport.Dolbeault.projectiveCechOpenSectionIso n j d q t).hom
  have he : e ≫ r ≫ v = ((Opens.map (Analytification.Base.analytificationMap X)).op ⋙ Q).map g := by
    change Q.map _ ≫ Q.map _ ≫ Q.map _ = Q.map _
    exact (congrArg (Q.map _ ≫ ·) (Q.map_comp _ _).symm).trans
      ((Q.map_comp _ _).symm.trans (congrArg Q.map (Subsingleton.elim _ _)))
  have hu : u ≫ ((Opens.map (Analytification.Base.analytificationMap X)).op ⋙ Q).map g = P.map g ≫ α.app (op B) :=
    (α.naturality g).symm
  let f := (ReferenceCechMap.Dolbeault.projectiveTwistOriginalCechMap n j d).f q
  let p := Pi.π (fun a : Fin (q + 1) → Fin (n + 1) => Q.obj
    (op (∏ᶜ fun k => Projective.Intersections.Dolbeault.projectiveStandardCover n (a k)))) t
  let s := Pi.π (fun a : Fin (q + 1) → Fin (n + 1) => P.obj
    (op (∏ᶜ fun k => Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n (a k)))) t
  have hp : f ≫ p = s ≫ u ≫ e ≫ r := projectiveTwistOriginalCechMap_proj n j d q t
  have ht : (f ≫ p) ≫ v = s ≫ u ≫ (e ≫ r ≫ v) :=
    (congrArg (· ≫ v) hp).trans ((Category.assoc s _ v).trans
      (congrArg (s ≫ ·) ((Category.assoc u _ v).trans (congrArg (u ≫ ·) (Category.assoc e r v)))))
  exact (Category.assoc f p v).symm.trans (ht.trans
    ((congrArg (fun h => s ≫ u ≫ h) he).trans (congrArg (s ≫ ·) hu)))

theorem projectiveTwistOriginalCechMap_factor_apply (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (t : Fin (q + 1) → Fin (n + 1)) (z : (ReferenceCechMap.Dolbeault.projectiveAlgebraicTwistCechComplex n j d).X q) :
    (Projective.CechSectionTransport.Dolbeault.projectiveCechOpenSectionIso n j d q t).hom
        (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj (Projective.Intersections.Dolbeault.projectiveStandardCover n) q
          ((ReferenceCechMap.Dolbeault.projectiveTwistOriginalCechMap n j d).f q z) t) =
      (Module.AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
        (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d)).app
          (op (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n (Finset.univ.image t)))
            ((ReferenceCechMap.Dolbeault.projectiveAlgebraicCechSectionIso n j d q t).hom
              (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).val.presheaf
                (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n) q z t)) := by
  have h := ConcreteCategory.congr_hom (projectiveTwistOriginalCechMap_factor n j d q t) z
  have hl := congrArg (Projective.CechSectionTransport.Dolbeault.projectiveCechOpenSectionIso n j d q t).hom
    (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv_apply (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj (Projective.Intersections.Dolbeault.projectiveStandardCover n) q
      ((ReferenceCechMap.Dolbeault.projectiveTwistOriginalCechMap n j d).f q z) t)
  have hr := congrArg (fun a => (Module.AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d)).app
        (op (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n (Finset.univ.image t)))
          ((ReferenceCechMap.Dolbeault.projectiveAlgebraicCechSectionIso n j d q t).hom a))
    (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv_apply (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).val.presheaf
      (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n) q z t)
  exact hl.trans (h.trans hr.symm)

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.ReferenceCechFactors.Dolbeault
