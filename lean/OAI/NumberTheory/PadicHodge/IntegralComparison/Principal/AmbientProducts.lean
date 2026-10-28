import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdditiveSections

/-! # Ambient Products -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AmbientProducts

noncomputable section

/-! Actual principal opens of an affine chart preserve nonempty finite
products in the ambient scheme. The terminal image remains the chart. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open OAI.AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)

theorem basicOpen_fin_prod (n : ℕ) (a : Fin (n+1) → Γ(X,U)) :
    X.basicOpen (∏ i, a i) = ⨅ i, X.basicOpen (a i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_succ, X.basicOpen_mul, ih]
    apply le_antisymm
    · apply le_iInf
      intro i
      refine Fin.cases inf_le_left (fun j => ?_) i
      exact inf_le_right.trans (iInf_le _ j)
    · exact le_inf (iInf_le _ 0) (le_iInf (fun j => iInf_le _ j.succ))

theorem basicOpen_prod {ι : Type v} [Fintype ι] [Nonempty ι] (a : ι → Γ(X,U)) :
    X.basicOpen (∏ i, a i) = ⨅ i, X.basicOpen (a i) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := ι))
  let e : Fin (n+1) ≃ ι := (Fintype.equivFinOfCardEq hn).symm
  rw [← e.prod_comp a, basicOpen_fin_prod]
  apply le_antisymm
  · apply le_iInf
    intro i
    obtain ⟨j, rfl⟩ := e.surjective i
    exact iInf_le _ j
  · exact le_iInf (fun j => iInf_le _ (e j))

def mappedConeIsLimit {J : Type v} [Category J] [Fintype J] [Nonempty J]
    (F : J ⥤ AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Γ(X,U)) :
    IsLimit ((AdditiveSections.opens U hU).mapCone
      (AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.finiteLimitCone Γ(X,U) F).cone) where
  lift c := homOfLE (by
    change c.pt ≤ X.basicOpen (∏ j, (F.obj j).val)
    rw [basicOpen_prod]
    exact le_iInf (fun j => leOfHom (c.π.app j)))

instance preserves_product {ι : Type v} [Fintype ι] [Nonempty ι]
    (a : ι → AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Γ(X,U)) :
    PreservesLimit (Discrete.functor a) (AdditiveSections.opens U hU) :=
  by
    let : Nonempty (Discrete ι) := ⟨⟨Classical.choice inferInstance⟩⟩
    exact preservesLimit_of_preserves_limit_cone
      (AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.finiteLimitCone Γ(X,U) (Discrete.functor a)).isLimit
        (mappedConeIsLimit U hU (Discrete.functor a))

instance preserves_family {ι : Type v} (W : ι → AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Γ(X,U)) :
    ∀ (n : ℕ) (z : Fin (n+1) → ι),
      PreservesLimit (Discrete.functor (W ∘ z)) (AdditiveSections.opens U hU) :=
  fun _ _ => preserves_product U hU _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AmbientProducts
