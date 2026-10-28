import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.GenerationLocus
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GenerationBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.GenerationResidues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.ResidueDetection

/-! # Generation Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GenerationLocus

noncomputable section

/-! The global generation open detects actual relation generation on every affine base, without a choice of global frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ α : Type u}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ] [Fintype α]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ] [DecidableEq α]
variable {S : Scheme.{u}} (R : CommRingCat.{u}) (f : Spec R ⟶ S)
variable (N : Module.Grassmannian R (ν → R) (Fintype.card ι))
variable (K : Module.Grassmannian R (μ → R) (Fintype.card κ)) (F : α → Matrix μ ν R)

theorem grassmannGenerationOpen_affine_iff
    (hF : ∀ t, Grassmann.IncidenceCondition.GrassmannIncidenceCondition (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f N)
      (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f K) ((F t).map (Scheme.ΓSpecIso R).inv.hom) (𝟙 (Over.mk f))) :
    Grassmann.GenerationOpen.grassmannGenerationOpen (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f N)
      (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f K)
      (fun t => (F t).map (Scheme.ΓSpecIso R).inv.hom) hF = ⊤ ↔
        K.toSubmodule = ⨆ t, N.toSubmodule.map (Matrix.toLin' (F t)) := by
  let U := Grassmann.GenerationOpen.grassmannGenerationOpen (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f N)
    (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f K)
    (fun t => (F t).map (Scheme.ΓSpecIso R).inv.hom) hF
  have hi : ∀ t, N.toSubmodule ≤ K.toSubmodule.comap (Matrix.toLin' (F t)) :=
    fun t => (IncidenceReflection.grassmannIncidence_affine_relations_iff R f N K (F t)).mp (hF t)
  change U = ⊤ ↔ _
  rw [AffineOpen.ResidueDetection.affineOpen_eq_top_iff_residuePoints, Coordinate.GenerationResidues.coordinate_generation_iff_residueFields N.toSubmodule K.toSubmodule F hi]
  apply forall_congr'
  intro p
  let A : CommRingCat.{u} := CommRingCat.of p.asIdeal.ResidueField
  let φ : R ⟶ A := CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField)
  let fA := Spec.map φ ≫ f
  let NA := HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap φ.hom N
  let KA := HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap φ.hom K
  let FA : α → Matrix μ ν A := fun t => (F t).map φ.hom
  have hiA : ∀ t, NA.toSubmodule ≤ KA.toSubmodule.comap (Matrix.toLin' (FA t)) :=
    fun t => Coordinate.IncidenceBaseChange.coordinateSubmoduleExtension_incidence φ.hom N.toSubmodule K.toSubmodule (F t) (hi t)
  have hA : ∀ t, Grassmann.IncidenceCondition.GrassmannIncidenceCondition (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv A fA NA)
      (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv A fA KA) ((FA t).map (Scheme.ΓSpecIso A).inv.hom) (𝟙 (Over.mk fA)) :=
    fun t => RelationsIncidence.grassmannIncidence_affine_relations A fA NA KA (FA t) (hiA t)
  have he : (Spec.map φ) ⁻¹ᵁ U = Grassmann.GenerationOpen.grassmannGenerationOpen
      (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv A fA NA) (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv A fA KA)
      (fun t => (FA t).map (Scheme.ΓSpecIso A).inv.hom) hA :=
    GenerationBaseChange.grassmannGenerationOpen_affine_baseChange R A φ f N K F hF hA
  exact (Iff.of_eq (congrArg (fun V => V = ⊤) he)).trans
    (Field.GenerationLocus.grassmannGenerationOpen_field_iff p.asIdeal.ResidueField fA NA KA FA hA)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GenerationLocus
