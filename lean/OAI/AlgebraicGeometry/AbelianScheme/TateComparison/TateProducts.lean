import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Functor

/-! # Tate Products -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TateProducts.Tate

noncomputable section

/-! Isomorphisms and products of actual point groups induce the expected
linear isomorphisms of their Tate inverse limits. -/

universe u
variable (q : ℕ) [Fact q.Prime] {H H' : Type u} [AddCommGroup H] [AddCommGroup H']

def mapEquiv (e : H ≃+ H') : Add.Tate.Module (H := H) q ≃ₗ[ℤ_[q]] Add.Tate.Module (H := H') q :=
  LinearEquiv.ofLinearMap (Add.Tate.map q e.toAddMonoidHom) (Add.Tate.map q e.symm.toAddMonoidHom)
    (by ext x n; exact e.apply_symm_apply (x.val n).val)
    (by ext x n; exact e.symm_apply_apply (x.val n).val)

def piEquiv {I : Type u} (G : I → Type u) [∀ i, AddCommGroup (G i)] :
    Add.Tate.Module (H := ∀ i, G i) q ≃ₗ[ℤ_[q]] ∀ i, Add.Tate.Module (H := G i) q where
  toFun x i := ⟨fun n => ⟨(x.val n).val i, congrFun (x.val n).property i⟩,
    fun n => Subtype.ext (congrFun (congrArg Subtype.val (x.property n)) i)⟩
  invFun x := ⟨fun n => ⟨fun i => ((x i).val n).val,
    funext fun i => ((x i).val n).property⟩,
    fun n => Subtype.ext (funext fun i => congrArg Subtype.val ((x i).property n))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' z x := by
    funext i
    apply Subtype.ext
    funext n
    exact Add.Tate.map_padic_smul q le_rfl ({
      toFun y := ⟨y.val i, congrFun y.property i⟩
      map_zero' := rfl
      map_add' _ _ := rfl } : Add.Tate.torsion q (∀ i, G i) n →+ Add.Tate.torsion q (G i) n) z (x.val n)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TateProducts.Tate
