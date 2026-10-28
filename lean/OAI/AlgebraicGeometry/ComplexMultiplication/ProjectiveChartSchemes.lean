import OAI.AlgebraicGeometry.ComplexMultiplication.ProjectiveChartNaturality

/-! # Projective Chart Schemes -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ProjectiveChartSchemes.ProjectiveCharts

noncomputable section

/-! # Actual affine chart schemes over arbitrary coefficient rings

The standard coordinate open is the spectrum of the polynomial ring in the
remaining variables. The isomorphism respects the actual structure morphism.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R : Type) [CommRing R]

abbrev projectiveSpace (n : ℕ) : Scheme := Proj (CMProjectiveCharts.ProjectiveCharts.projectiveGrading R n)

/-- The actual morphism to the spectrum of the coefficient ring. -/
def projectiveSpaceToBase (n : ℕ) : projectiveSpace R n ⟶ Spec (.of R) :=
  Proj.toSpecZero (CMProjectiveCharts.ProjectiveCharts.projectiveGrading R n) ≫
    Spec.map (CommRingCat.ofHom (CMProjectiveCharts.ProjectiveCharts.degreeZeroConstants R n).toRingHom)

theorem projectiveSpaceToBase_chart (n : ℕ) (m : ℕ)
    (f : CMProjectiveCharts.ProjectiveCharts.homogeneousCoordinateRing R n) (hf : f ∈ CMProjectiveCharts.ProjectiveCharts.projectiveGrading R n m) (hm : 0 < m) :
    Proj.awayι (CMProjectiveCharts.ProjectiveCharts.projectiveGrading R n) f hf hm ≫ projectiveSpaceToBase R n =
      Spec.map (CommRingCat.ofHom
        ((HomogeneousLocalization.fromZeroRingHom (CMProjectiveCharts.ProjectiveCharts.projectiveGrading R n) (Submonoid.powers f)).comp
          (CMProjectiveCharts.ProjectiveCharts.degreeZeroConstants R n).toRingHom)) := by
  rw [projectiveSpaceToBase, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

abbrev projectiveCoordinateOpen (n : ℕ) (i : Fin (n + 1)) : (projectiveSpace R n).Opens :=
  Proj.basicOpen (CMProjectiveCharts.ProjectiveCharts.projectiveGrading R n) (MvPolynomial.X i)

def projectiveCoordinateAffineCover (n : ℕ) : (projectiveSpace R n).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (CMProjectiveCharts.ProjectiveCharts.projectiveGrading R n)
    (fun (i : Fin (n + 1)) => MvPolynomial.X i) (m := fun _ => 1)
    (fun i => CMProjectiveCharts.ProjectiveCharts.projectiveVariable_homogeneous R n i) (fun _ => by decide)
    (ProjectiveChartNaturality.ProjectiveCharts.projective_irrelevant_eq_coordinateIdeal R n).le

@[simp]
theorem projectiveChartRingEquiv_coe (n : ℕ) (i : Fin (n + 1)) :
    (CMProjectiveCharts.ProjectiveCharts.projectiveChartRingEquiv R n i : CMProjectiveCharts.ProjectiveCharts.projectiveChartRing R n i →+* CMProjectiveCharts.ProjectiveCharts.projectiveChartPolynomial R n i) =
      CMProjectiveCharts.ProjectiveCharts.projectiveChartToPolynomial R n i := by
  ext x
  rfl

/-- The standard chart isomorphism uses the actual degree-zero homogeneous localization. -/
def projectiveCoordinateIsoSpec (n : ℕ) (i : Fin (n + 1)) :
    (projectiveCoordinateOpen R n i).toScheme ≅ Spec (.of (CMProjectiveCharts.ProjectiveCharts.projectiveChartPolynomial R n i)) :=
  Proj.basicOpenIsoSpec (CMProjectiveCharts.ProjectiveCharts.projectiveGrading R n) (MvPolynomial.X i)
      (CMProjectiveCharts.ProjectiveCharts.projectiveVariable_homogeneous R n i) (by decide : 0 < 1) ≪≫
    Scheme.Spec.mapIso (CMProjectiveCharts.ProjectiveCharts.projectiveChartRingEquiv R n i).symm.toCommRingCatIso.op

@[reassoc]
theorem projectiveCoordinateIsoSpec_inv_ι (n : ℕ) (i : Fin (n + 1)) :
    (projectiveCoordinateIsoSpec R n i).inv ≫ (projectiveCoordinateOpen R n i).ι =
      Spec.map (CommRingCat.ofHom (CMProjectiveCharts.ProjectiveCharts.projectiveChartToPolynomial R n i)) ≫
        Proj.awayι (CMProjectiveCharts.ProjectiveCharts.projectiveGrading R n) (MvPolynomial.X i)
          (CMProjectiveCharts.ProjectiveCharts.projectiveVariable_homogeneous R n i) (by decide : 0 < 1) := by
  simp [projectiveCoordinateIsoSpec, Proj.awayι, Category.assoc]

@[reassoc]
theorem projectiveCoordinateIsoSpec_inv_over (n : ℕ) (i : Fin (n + 1)) :
    (projectiveCoordinateIsoSpec R n i).inv ≫ (projectiveCoordinateOpen R n i).ι ≫
      projectiveSpaceToBase R n =
        Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* CMProjectiveCharts.ProjectiveCharts.projectiveChartPolynomial R n i)) := by
  rw [projectiveCoordinateIsoSpec_inv_ι_assoc, projectiveSpaceToBase_chart, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact CMProjectiveCharts.ProjectiveCharts.projectiveChartToPolynomial_constants R n i c

/-- The same chart map from the actual polynomial spectrum. -/
def projectiveAffineChartMap (n : ℕ) (i : Fin (n + 1)) :
    Spec (.of (CMProjectiveCharts.ProjectiveCharts.projectiveChartPolynomial R n i)) ⟶ projectiveSpace R n :=
  (projectiveCoordinateIsoSpec R n i).inv ≫ (projectiveCoordinateOpen R n i).ι

instance CMProjectiveChartSchemes.localInstance1 (n : ℕ) (i : Fin (n + 1)) : IsOpenImmersion (projectiveAffineChartMap R n i) := by
  dsimp [projectiveAffineChartMap]
  infer_instance

@[reassoc]
theorem projectiveAffineChartMap_over (n : ℕ) (i : Fin (n + 1)) :
    projectiveAffineChartMap R n i ≫ projectiveSpaceToBase R n =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* CMProjectiveCharts.ProjectiveCharts.projectiveChartPolynomial R n i)) :=
  projectiveCoordinateIsoSpec_inv_over R n i

/-- The actual finite open cover, expressed in polynomial affine coordinates. -/
def projectivePolynomialOpenCover (n : ℕ) : (projectiveSpace R n).OpenCover :=
  (projectiveCoordinateAffineCover R n).openCover.copy (Fin (n + 1))
    (fun i => Spec (.of (CMProjectiveCharts.ProjectiveCharts.projectiveChartPolynomial R n i)))
    (fun i => projectiveAffineChartMap R n i) (Equiv.refl _)
    (fun i => Scheme.Spec.mapIso (CMProjectiveCharts.ProjectiveCharts.projectiveChartRingEquiv R n i).toCommRingCatIso.op)
    (fun i => by
      change (projectiveCoordinateIsoSpec R n i).inv ≫ (projectiveCoordinateOpen R n i).ι =
        Spec.map (CommRingCat.ofHom (CMProjectiveCharts.ProjectiveCharts.projectiveChartRingEquiv R n i).toRingHom) ≫
          Proj.awayι (CMProjectiveCharts.ProjectiveCharts.projectiveGrading R n) (MvPolynomial.X i)
            (CMProjectiveCharts.ProjectiveCharts.projectiveVariable_homogeneous R n i) (by decide : 0 < 1)
      have h : (CMProjectiveCharts.ProjectiveCharts.projectiveChartRingEquiv R n i).toRingHom = CMProjectiveCharts.ProjectiveCharts.projectiveChartToPolynomial R n i := by
        ext c
        rfl
      rw [projectiveCoordinateIsoSpec_inv_ι, h])

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ProjectiveChartSchemes.ProjectiveCharts
