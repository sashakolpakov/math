import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsLocalRigidity

/-! # Pointwise Fiber Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PointwiseFiberRigidity.Construction

noncomputable section

/-! If functions on every restricted fiber family come from the
base, a map that is pointwise constant on fibers factors through its section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsLocalRigidity

universe u

theorem map_eq_of_pointwise_fiber_constancy
    {X S Y : Scheme.{u}} (p : X ⟶ S) [UniversallyClosed p]
    (hp : ∀ V : S.Opens, IsIso (p ∣_ V).appTop)
    (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 _) (f : X ⟶ Y)
    (hpoint : ∀ x : X, f x = f (σ (p x))) : f = p ≫ σ ≫ f := by
  choose V hs he using fun s : S =>
    AbelianModuli.HilbertConstruction.Global.FunctionsLocalRigidity.globalFunctions_localRigidity p hp σ hσ f s (f (σ s))
      (fun x hx => (hpoint x).trans (congrArg (fun t => f (σ t)) hx))
  let C : X.OpenCover.{u} := {
    I₀ := S
    X := fun s => (p ⁻¹ᵁ V s).toScheme
    f := fun s => (p ⁻¹ᵁ V s).ι
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun x => ⟨p x, ⟨x, hs (p x)⟩, rfl⟩, inferInstance⟩ }
  exact C.hom_ext f (p ≫ σ ≫ f) he

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PointwiseFiberRigidity.Construction
