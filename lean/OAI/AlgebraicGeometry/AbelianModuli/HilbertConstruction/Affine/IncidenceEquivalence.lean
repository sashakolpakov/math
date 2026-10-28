import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IncidenceReflection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IncidenceLifting

/-! # Incidence Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IncidenceEquivalence

noncomputable section

/-! A global affine criterion for incidence under arbitrary parameter maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ : Type u}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ]
variable {S : Scheme.{u}} {M T : Over S}
variable (q : M ⟶ Grassmann.ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S)
variable (k : M ⟶ Grassmann.ParameterScheme.grassmannParameterScheme (ι := κ) (ν := μ) S)
variable (F : Matrix μ ν Γ(M.left, ⊤))

theorem grassmannIncidenceCondition_pullback (x : T ⟶ M) :
    Grassmann.IncidenceCondition.GrassmannIncidenceCondition q k F x ↔
      Grassmann.IncidenceCondition.GrassmannIncidenceCondition (x ≫ q) (x ≫ k) (F.map x.left.appTop.hom) (𝟙 T) := by
  rw [← Grassmann.IncidenceCondition.grassmannIncidenceIdeal_vanish_iff, ← Grassmann.IncidenceCondition.grassmannIncidenceIdeal_vanish_iff]
  change (Grassmann.IncidenceScheme.grassmannIncidenceIdeal q k F).comap x.left = ⊥ ↔
    (Grassmann.IncidenceScheme.grassmannIncidenceIdeal (x ≫ q) (x ≫ k) (F.map x.left.appTop.hom)).comap (𝟙 T.left) = ⊥
  rw [Scheme.IdealSheafData.comap_id, Grassmann.IncidenceChartRecognition.grassmannIncidenceIdeal_baseChange]

theorem grassmannIncidenceCondition_affine_iff
    (R : CommRingCat.{u}) (f : Spec R ⟶ S) (x : Over.mk f ⟶ M)
    (N : Module.Grassmannian R (ν → R) (Fintype.card ι))
    (K : Module.Grassmannian R (μ → R) (Fintype.card κ))
    (hN : x ≫ q = Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f N)
    (hK : x ≫ k = Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f K)
    (F₀ : Matrix μ ν R)
    (hF : F.map x.left.appTop.hom = F₀.map (Scheme.ΓSpecIso R).inv.hom) :
    Grassmann.IncidenceCondition.GrassmannIncidenceCondition q k F x ↔
      N.toSubmodule ≤ K.toSubmodule.comap (Matrix.toLin' F₀) := by
  rw [grassmannIncidenceCondition_pullback, hN, hK, hF]
  exact IncidenceReflection.grassmannIncidence_affine_relations_iff R f N K F₀

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IncidenceEquivalence
