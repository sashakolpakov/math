import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.GenerationOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ParameterNaturality

/-! # Generation Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GenerationBaseChange

noncomputable section

/-! The generation open for actual affine quotient data commutes with their explicit coefficient extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ α : Type u}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ] [Fintype α]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ] [DecidableEq α]

theorem grassmannGenerationOpen_congr {S : Scheme.{u}} {M : Over S}
    {q q' : M ⟶ Grassmann.ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S}
    {k k' : M ⟶ Grassmann.ParameterScheme.grassmannParameterScheme (ι := κ) (ν := μ) S}
    {F F' : α → Matrix μ ν Γ(M.left, ⊤)} (hq : q = q') (hk : k = k') (hFF : F = F')
    (hF : ∀ t, Grassmann.IncidenceCondition.GrassmannIncidenceCondition q k (F t) (𝟙 M))
    (hF' : ∀ t, Grassmann.IncidenceCondition.GrassmannIncidenceCondition q' k' (F' t) (𝟙 M)) :
    Grassmann.GenerationOpen.grassmannGenerationOpen q k F hF = Grassmann.GenerationOpen.grassmannGenerationOpen q' k' F' hF' := by
  subst q'
  subst k'
  subst F'
  rfl

variable {S : Scheme.{u}} (R A : CommRingCat.{u}) (φ : R ⟶ A) (f : Spec R ⟶ S)
variable (N : Module.Grassmannian R (ν → R) (Fintype.card ι))
variable (K : Module.Grassmannian R (μ → R) (Fintype.card κ)) (F : α → Matrix μ ν R)

theorem grassmannGenerationOpen_affine_baseChange
    (hF : ∀ t, Grassmann.IncidenceCondition.GrassmannIncidenceCondition (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f N)
      (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f K) ((F t).map (Scheme.ΓSpecIso R).inv.hom) (𝟙 (Over.mk f)))
    (hF' : ∀ t, Grassmann.IncidenceCondition.GrassmannIncidenceCondition
      (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv A (Spec.map φ ≫ f) (HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap φ.hom N))
      (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv A (Spec.map φ ≫ f) (HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap φ.hom K))
      (((F t).map φ.hom).map (Scheme.ΓSpecIso A).inv.hom) (𝟙 (Over.mk (Spec.map φ ≫ f)))) :
    (Spec.map φ) ⁻¹ᵁ Grassmann.GenerationOpen.grassmannGenerationOpen
      (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f N) (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f K)
      (fun t => (F t).map (Scheme.ΓSpecIso R).inv.hom) hF =
        Grassmann.GenerationOpen.grassmannGenerationOpen
          (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv A (Spec.map φ ≫ f) (HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap φ.hom N))
          (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv A (Spec.map φ ≫ f) (HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap φ.hom K))
          (fun t => ((F t).map φ.hom).map (Scheme.ΓSpecIso A).inv.hom) hF' := by
  let x : Over.mk (Spec.map φ ≫ f) ⟶ Over.mk f := Over.homMk (Spec.map φ) rfl
  let q : Over.mk f ⟶ Grassmann.ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S :=
    Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f N
  let k : Over.mk f ⟶ Grassmann.ParameterScheme.grassmannParameterScheme (ι := κ) (ν := μ) S :=
    Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f K
  let G : α → Matrix μ ν Γ(Spec R, ⊤) := fun t => (F t).map (Scheme.ΓSpecIso R).inv.hom
  have hq : x ≫ q = Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv A (Spec.map φ ≫ f) (HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap φ.hom N) :=
    (Grassmann.ParameterNaturality.grassmannParameter_classifying_naturality R A φ.hom f N).symm
  have hk : x ≫ k = Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv A (Spec.map φ ≫ f) (HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap φ.hom K) :=
    (Grassmann.ParameterNaturality.grassmannParameter_classifying_naturality R A φ.hom f K).symm
  have hG : (fun t => (G t).map x.left.appTop.hom) =
      (fun t => ((F t).map φ.hom).map (Scheme.ΓSpecIso A).inv.hom) := by
    funext t
    ext i j
    exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality φ) (F t i j)).symm
  exact (Grassmann.GenerationOpen.grassmannGenerationOpen_baseChange (q := q) (k := k) G hF x).trans
    (grassmannGenerationOpen_congr hq hk hG _ hF')

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GenerationBaseChange
