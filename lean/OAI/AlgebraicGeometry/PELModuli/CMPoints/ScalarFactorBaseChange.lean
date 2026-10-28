import OAI.AlgebraicGeometry.PELModuli.CMPoints.TorsionFactorIso
import OAI.AlgebraicGeometry.PELModuli.CMPoints.GroupMapReflection

/-! # Scalar Factor Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! Scalar factorizations commute with base change and reflect from
dominant fibers of smooth arithmetic models. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem ScalarFactorBaseChange.abelian_multiplication_pullback {S T : Scheme.{0}} {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (u : T ⟶ S) (n : ℕ) :
    (Over.pullback u).map (A.multiplication n) = (A.pullback u).multiplication n := by
  have h := map_pow ((Over.pullback u).homMonoidHom (X := A.scheme) (M := A.scheme)) (𝟙 A.scheme) n
  change (Over.pullback u).map ((𝟙 A.scheme) ^ n) = ((Over.pullback u).map (𝟙 A.scheme)) ^ n at h
  exact h.trans (congrArg (fun f => f ^ n) ((Over.pullback u).map_id A.scheme))

def TorsionFactorIso.AbelianScalarFactorization.pullback
    {S T : Scheme.{0}} {I : Type} [Fintype I] {g : ℕ} {d : I → ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : ∀ i, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (d i) S}
    (D : TorsionFactorIso.AbelianScalarFactorization A B) (u : T ⟶ S) :
    TorsionFactorIso.AbelianScalarFactorization (A.pullback u) (fun i => (B i).pullback u) := by
  let (i : I) : IsMonHom (D.forward i) := D.forward_group i
  let (i : I) : IsMonHom (D.backward i) := D.backward_group i
  refine {
    multiplier := D.multiplier
    positive := D.positive
    forward := fun i => (Over.pullback u).map (D.forward i)
    backward := fun i => (Over.pullback u).map (D.backward i)
    forward_group := fun i => inferInstanceAs (IsMonHom ((Over.pullback u).map (D.forward i)))
    backward_group := fun i => inferInstanceAs (IsMonHom ((Over.pullback u).map (D.backward i)))
    diagonal := ?_
    offDiagonal := ?_
    total := ?_ }
  · intro i
    exact ((Over.pullback u).map_comp (D.backward i) (D.forward i)).symm.trans
      ((congrArg (Over.pullback u).map (D.diagonal i)).trans
        (ScalarFactorBaseChange.abelian_multiplication_pullback (B i) u D.multiplier))
  · intro i j hij
    exact ((Over.pullback u).map_comp (D.backward i) (D.forward j)).symm.trans
      ((congrArg (Over.pullback u).map (D.offDiagonal i j hij)).trans (Over.pullback u).map_one)
  · have h := map_prod ((Over.pullback u).homMonoidHom (X := A.scheme) (M := A.scheme))
      (fun i => D.forward i ≫ D.backward i) Finset.univ
    change (Over.pullback u).map (∏ i, D.forward i ≫ D.backward i) =
      ∏ i, (Over.pullback u).map (D.forward i ≫ D.backward i) at h
    simp_rw [Functor.map_comp] at h
    exact h.symm.trans ((congrArg (Over.pullback u).map D.total).trans
      (ScalarFactorBaseChange.abelian_multiplication_pullback A u D.multiplier))

def ScalarFactorBaseChange.abelianScalarFactorizationOfDominant
    {S T : Scheme.{0}} [IsReduced S] [IsLocallyNoetherian S]
    (u : T ⟶ S) [IsDominant u] {I : Type} [Fintype I] {g : ℕ} {d : I → ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : ∀ i, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (d i) S)
    (D : TorsionFactorIso.AbelianScalarFactorization (A.pullback u) (fun i => (B i).pullback u))
    (f : ∀ i, A.scheme ⟶ (B i).scheme) (r : ∀ i, (B i).scheme ⟶ A.scheme)
    (hf : ∀ i, (Over.pullback u).map (f i) = D.forward i)
    (hr : ∀ i, (Over.pullback u).map (r i) = D.backward i) :
    TorsionFactorIso.AbelianScalarFactorization A B := by
  refine {
    multiplier := D.multiplier
    positive := D.positive
    forward := f
    backward := r
    forward_group := ?_
    backward_group := ?_
    diagonal := ?_
    offDiagonal := ?_
    total := ?_ }
  · intro i
    let : IsMonHom ((Over.pullback u).map (f i)) := (hf i).symm ▸ D.forward_group i
    exact GroupMapReflection.isMonHom_of_dominant_baseChange u (f i)
  · intro i
    let : IsMonHom ((Over.pullback u).map (r i)) := (hr i).symm ▸ D.backward_group i
    exact GroupMapReflection.isMonHom_of_dominant_baseChange u (r i)
  · intro i
    apply IntegralModel.GenericIdentities.smooth_hom_eq_of_dominant_base_change u
    rw [Functor.map_comp, hf, hr]
    exact (D.diagonal i).trans (ScalarFactorBaseChange.abelian_multiplication_pullback (B i) u D.multiplier).symm
  · intro i j hij
    apply IntegralModel.GenericIdentities.smooth_hom_eq_of_dominant_base_change u
    rw [Functor.map_comp, hf, hr]
    exact (D.offDiagonal i j hij).trans (Over.pullback u).map_one.symm
  · apply IntegralModel.GenericIdentities.smooth_hom_eq_of_dominant_base_change u
    have h := map_prod ((Over.pullback u).homMonoidHom (X := A.scheme) (M := A.scheme))
      (fun i => f i ≫ r i) Finset.univ
    change (Over.pullback u).map (∏ i, f i ≫ r i) =
      ∏ i, (Over.pullback u).map (f i ≫ r i) at h
    rw [h, ScalarFactorBaseChange.abelian_multiplication_pullback]
    simp_rw [Functor.map_comp, hf, hr]
    exact D.total

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
