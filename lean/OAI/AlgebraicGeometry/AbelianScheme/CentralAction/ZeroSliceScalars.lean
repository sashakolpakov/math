import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LineGeometricExt
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.NormalizedLineIso

/-! # Zero Slice Scalars -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ZeroSliceScalars.Construction

noncomputable section

/-! The zero slice detects global functions on products with a connected
reduced proper scheme. This supplies normalization rigidity on the finite
etale overlap of an isogeny. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {k : Type} [Field k] [IsAlgClosed k]

theorem zeroSlice_global_function_injective
    (A B : Over (Spec (.of k)))
    [IsProper A.hom] [ConnectedSpace A.left] [IsReduced A.left]
    [IsReduced (A ⊗ B).left] [LocallyOfFiniteType (A ⊗ B).hom]
    (a₀ : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    Function.Injective (lift (toUnit B ≫ a₀) (𝟙 B)).left.appTop := by
  let z : B ⟶ A ⊗ B := lift (toUnit B ≫ a₀) (𝟙 B)
  intro r s hrs
  apply LineGeometricExt.Construction.global_section_ext_rational (A ⊗ B) r s
  intro p
  let a := p ≫ fst A B
  let b := p ≫ snd A B
  let t : A ⟶ A ⊗ B := lift (𝟙 A) (toUnit A ≫ b)
  have hunit : toUnit (Over.mk (𝟙 (Spec (.of k)))) = 𝟙 _ := Subsingleton.elim _ _
  have hzt : a₀ ≫ t = b ≫ z := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [t, z, hunit]
  have hpt : a ≫ t = p := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [t, a, b, hunit]
  have ht : t.left.appTop r = t.left.appTop s := by
    let := (Quotients.FiniteDescent.ProperFunctionsEq.Construction.ProperFunctions.globalSections_isField A).toField
    have : Nontrivial Γ((𝟙_ (Over (Spec (.of k)))).left, ⊤) :=
      inferInstanceAs (Nontrivial Γ(Spec (.of k), ⊤))
    apply a₀.left.appTop.hom.injective
    have hh : z.left.appTop r = z.left.appTop s := hrs
    have H := congrArg (fun v => b.left.appTop v) hh
    have he := congrArg (fun f => f.left) hzt
    simp only [Over.comp_left] at he
    simpa only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, he] using H
  have he := congrArg (fun f => f.left) hpt
  simp only [Over.comp_left] at he
  rw [← he, Scheme.Hom.comp_appTop]
  exact congrArg (fun v => a.left.appTop v) ht

theorem zeroSlice_global_function_bijective
    (A B : Over (Spec (.of k)))
    [IsProper A.hom] [ConnectedSpace A.left] [IsReduced A.left]
    [IsReduced (A ⊗ B).left] [LocallyOfFiniteType (A ⊗ B).hom]
    (a₀ : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    Function.Bijective (lift (toUnit B ≫ a₀) (𝟙 B)).left.appTop := by
  refine ⟨zeroSlice_global_function_injective A B a₀, ?_⟩
  intro r
  refine ⟨(snd A B).left.appTop r, ?_⟩
  change (ConcreteCategory.hom ((snd A B).left.appTop ≫
    (lift (toUnit B ≫ a₀) (𝟙 B)).left.appTop)) r = r
  rw [← Scheme.Hom.comp_appTop, ← Over.comp_left, lift_snd, Over.id_left,
    Scheme.Hom.id_appTop]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ZeroSliceScalars.Construction
