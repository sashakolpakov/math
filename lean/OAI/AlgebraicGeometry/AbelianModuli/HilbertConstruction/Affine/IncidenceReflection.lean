import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RelationsIncidence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoverCoefficientDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.RelationDetection

/-! # Incidence Reflection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IncidenceReflection

noncomputable section

/-!
The global incidence scheme condition on affine quotient points is equivalent
to actual containment of their relation modules. No global frames are needed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ : Type u}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ]
variable {S : Scheme.{u}} (R : CommRingCat.{u}) (f : Spec R ⟶ S)
variable (N : Module.Grassmannian R (ν → R) (Fintype.card ι))
variable (K : Module.Grassmannian R (μ → R) (Fintype.card κ)) (F : Matrix μ ν R)

theorem grassmannIncidence_affine_relations_iff :
    Grassmann.IncidenceCondition.GrassmannIncidenceCondition (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f N)
      (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f K) (F.map (Scheme.ΓSpecIso R).inv.hom)
        (𝟙 (Over.mk f)) ↔ N.toSubmodule ≤ K.toSubmodule.comap (Matrix.toLin' F) := by
  constructor
  · intro h
    let T : Over S := Over.mk f
    let q := Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f N
    let k := Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f K
    let F' := F.map (Scheme.ΓSpecIso R).inv.hom
    let D := Grassmann.PairChartCover.grassmannPairChartCover q k
    let E := D.affineRefinement
    let C : Scheme.AffineOpenCover (Spec R) := D.cover.affineRefinement
    have hI : Grassmann.IncidenceScheme.grassmannIncidenceIdeal q k F' = ⊥ :=
      (Scheme.IdealSheafData.comap_id _).symm.trans
        ((Grassmann.IncidenceCondition.grassmannIncidenceIdeal_vanish_iff q k F' (𝟙 T)).mpr h)
    apply Coordinate.RelationDetection.coordinateIncidence_of_jointly_detect_zero (fun i => C.X i)
      (CoverCoefficientDetection.affineCoverCoefficientMap R C) (CoverCoefficientDetection.affineCoverCoefficientMap_detect_zero R C)
      N.toSubmodule K.toSubmodule F
    intro i
    change D.affineCover.I₀ at i
    let A := D.affineCoverRing i
    let g : Spec A ⟶ S := E.cover.f i ≫ f
    let x : Over.mk g ⟶ T := Over.homMk (E.cover.f i) rfl
    let φ := ParameterNaturality.affineTestCoefficientMap R A f g x
    let N' := HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap φ N
    let K' := HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap φ K
    have hN : x ≫ q = Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv A g N' :=
      (ParameterNaturality.grassmannParameterAffine_naturality R A f g x N).symm
    have hK : x ≫ k = Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv A g K' :=
      (ParameterNaturality.grassmannParameterAffine_naturality R A f g x K).symm
    let v : Over.mk g ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart (E.sourceColumns i) S := E.sourceLift i
    let w : Over.mk g ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart (E.targetColumns i) S := E.targetLift i
    have hv : v ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap (E.sourceColumns i) S = x ≫ q := E.source_fac i
    have hw : w ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap (E.targetColumns i) S = x ≫ k := E.target_fac i
    have hi : Grassmann.IncidenceCondition.GrassmannIncidenceCondition q k F' x :=
      (Grassmann.IncidenceCondition.grassmannIncidenceIdeal_vanish_iff q k F' x).mp
        ((congrArg (fun I : (Spec R).IdealSheafData => I.comap x.left) hI).trans
          (Scheme.IdealSheafData.comap_bot x.left))
    exact (IncidenceCriterion.grassmannIncidenceCondition_affine_chart q k F' A g x N' K' hN hK
      (E.sourceColumns i) (E.targetColumns i) v w hv hw (F.map φ)
      (ParameterNaturality.affineTestCoefficientMap_matrix R A f g x F)).mp hi
  · exact RelationsIncidence.grassmannIncidence_affine_relations R f N K F

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IncidenceReflection
