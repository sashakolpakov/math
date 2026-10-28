import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RelationsIncidence

/-! # Incidence Lifting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IncidenceLifting

noncomputable section

/-! Compatible actual affine quotient data lift to the constructed global incidence scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ : Type u}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ]
variable {S : Scheme.{u}} {M : Over S}
variable (q : M ⟶ Grassmann.ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S)
variable (k : M ⟶ Grassmann.ParameterScheme.grassmannParameterScheme (ι := κ) (ν := μ) S)
variable (F : Matrix μ ν Γ(M.left, ⊤))

theorem grassmannIncidenceCondition_of_affine_relations
    (R : CommRingCat.{u}) (f : Spec R ⟶ S) (x : Over.mk f ⟶ M)
    (N : Module.Grassmannian R (ν → R) (Fintype.card ι))
    (K : Module.Grassmannian R (μ → R) (Fintype.card κ))
    (hN : x ≫ q = Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f N)
    (hK : x ≫ k = Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f K)
    (F₀ : Matrix μ ν R)
    (hF : F.map x.left.appTop.hom = F₀.map (Scheme.ΓSpecIso R).inv.hom)
    (h : N.toSubmodule ≤ K.toSubmodule.comap (Matrix.toLin' F₀)) :
    Grassmann.IncidenceCondition.GrassmannIncidenceCondition q k F x := by
  have he : Grassmann.IncidenceScheme.grassmannIncidenceIdeal (x ≫ q) (x ≫ k) (F.map x.left.appTop.hom) =
      Grassmann.IncidenceScheme.grassmannIncidenceIdeal (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f N)
        (Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv R f K) (F₀.map (Scheme.ΓSpecIso R).inv.hom) := by
    rw [hN, hK, hF]
  exact (Grassmann.IncidenceCondition.grassmannIncidenceIdeal_vanish_iff q k F x).mp
    ((Grassmann.IncidenceChartRecognition.grassmannIncidenceIdeal_baseChange F x).trans
      (he.trans (RelationsIncidence.grassmannIncidenceIdeal_eq_bot_of_affine_relations R f N K F₀ h)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IncidenceLifting
