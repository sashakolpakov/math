import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IncidenceCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ParameterNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.PairAffineCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.IncidenceUniversality

/-! # Relations Incidence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RelationsIncidence

noncomputable section

/-!
Actual compatible affine quotient relations satisfy the global incidence
scheme equations. The proof uses the constructed common affine chart cover,
without assuming the quotient modules have global normalized frames.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ : Type u}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ]
variable {S : Scheme.{u}} (R : CommRingCat.{u}) (f : Spec R ⟶ S)
variable (N : Module.Grassmannian R (ν → R) (Fintype.card ι))
variable (K : Module.Grassmannian R (μ → R) (Fintype.card κ)) (F : Matrix μ ν R)

theorem grassmannIncidenceIdeal_eq_bot_of_affine_relations
    (h : N.toSubmodule ≤ K.toSubmodule.comap (Matrix.toLin' F)) :
    Grassmann.IncidenceScheme.grassmannIncidenceIdeal (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f N)
      (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f K) (F.map (Scheme.ΓSpecIso R).inv.hom) = ⊥ := by
  let T : Over S := Over.mk f
  let q := Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f N
  let k := Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f K
  let D := Grassmann.PairChartCover.grassmannPairChartCover q k
  let E := D.affineRefinement
  apply ClosedFamily.OpenEquality.ideal_eq_of_open_cover E.cover
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
  have hi : Grassmann.IncidenceCondition.GrassmannIncidenceCondition q k (F.map (Scheme.ΓSpecIso R).inv.hom) x :=
    (IncidenceCriterion.grassmannIncidenceCondition_affine_chart q k _ A g x N' K' hN hK
      (E.sourceColumns i) (E.targetColumns i) v w hv hw (F.map φ)
      (ParameterNaturality.affineTestCoefficientMap_matrix R A f g x F)).mpr
        (Coordinate.IncidenceBaseChange.coordinateSubmoduleExtension_incidence φ N.toSubmodule K.toSubmodule F h)
  exact ((Grassmann.IncidenceCondition.grassmannIncidenceIdeal_vanish_iff q k _ x).mpr hi).trans
    (Scheme.IdealSheafData.comap_bot (E.cover.f i)).symm

theorem grassmannIncidence_affine_relations
    (h : N.toSubmodule ≤ K.toSubmodule.comap (Matrix.toLin' F)) :
    Grassmann.IncidenceCondition.GrassmannIncidenceCondition (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f N)
      (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f K) (F.map (Scheme.ΓSpecIso R).inv.hom)
        (𝟙 (Over.mk f)) := by
  let q := Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f N
  let k := Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f K
  let F' := F.map (Scheme.ΓSpecIso R).inv.hom
  have hI : Grassmann.IncidenceScheme.grassmannIncidenceIdeal q k F' = ⊥ :=
    grassmannIncidenceIdeal_eq_bot_of_affine_relations R f N K F h
  have hv : (Grassmann.IncidenceScheme.grassmannIncidenceIdeal q k F').comap (𝟙 (Spec R)) = ⊥ :=
    (Scheme.IdealSheafData.comap_id _).trans hI
  exact (Grassmann.IncidenceCondition.grassmannIncidenceIdeal_vanish_iff q k F' (𝟙 (Over.mk f))).mp hv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RelationsIncidence
