import OAI.RepresentationTheory.Theta.Geometric.CechAxisBaseChange
import OAI.RepresentationTheory.Theta.Geometric.Normalized.KernelBaseChange

/-! # Cech Axis Tensor Comparison -/

namespace OAI.RepresentationTheory.Theta.Geometric.CechAxisTensorComparison

noncomputable section

/-! The complete tensor comparison identifies actual axis evaluation
with scalar extension of the original degree-zero functional. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

universe u

theorem cechAxisFunctional_tensorBaseChange
    {X Y S T : Scheme.{u}} (f : Y ⟶ X) (b : T ⟶ Y) (g : T ⟶ S) (s : S ⟶ X)
    (h : b ≫ f = g ≫ s) (π : X ⟶ S) (ρ : Y ⟶ T) (hπ : f ≫ π = ρ ≫ g)
    (hs : s ≫ π = 𝟙 S) (hb : b ≫ ρ = 𝟙 T)
    (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    {I : Type u} [LinearOrder I] (U : I → X.Opens) (i : I)
    (hi : (⊤ : S.Opens) ≤ s ⁻¹ᵁ AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0
      (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i)) :
    letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    ∀ z : Γ(T, ⊤) ⊗[Γ(S, ⊤)] (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).X 0,
      CechAxisFunctional.cechAxisFunctional ρ b hb ((Scheme.Modules.pullback f).obj M)
        (AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b g s h M r) (fun j => f ⁻¹ᵁ U j) i
        (CechAxisBaseChange.cechAxisOpen_baseChange f b g s h U i hi)
          ((AlgebraicGeometry.Quotients.FiniteDescent.CechBaseTmul.Construction.CechBaseChangeMap.map f π ρ g hπ M U).f 0 z) =
        Normalized.KernelBaseChange.scalarFunctionalBaseChange Γ(T, ⊤) (CechAxisFunctional.cechAxisFunctional π s hs M r U i hi) z := by
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  let v := CechAxisFunctional.cechAxisFunctional π s hs M r U i hi
  let w := CechAxisFunctional.cechAxisFunctional ρ b hb ((Scheme.Modules.pullback f).obj M)
    (AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b g s h M r) (fun j => f ⁻¹ᵁ U j) i
    (CechAxisBaseChange.cechAxisOpen_baseChange f b g s h U i hi)
  let F : Γ(T, ⊤) ⊗[Γ(S, ⊤)] (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).X 0 →ₗ[Γ(T, ⊤)] Γ(T, ⊤) :=
    w.comp ((AlgebraicGeometry.Quotients.FiniteDescent.CechBaseTmul.Construction.CechBaseChangeMap.map f π ρ g hπ M U).f 0).hom
  intro z
  change F z = Normalized.KernelBaseChange.scalarFunctionalBaseChange Γ(T, ⊤) v z
  induction z using TensorProduct.inductionOn with
  | tmul a z =>
      rw [TensorProduct.tmul_eq_smul_one_tmul, _root_.map_smul, _root_.map_smul]
      apply congrArg (fun x => a • x)
      change w ((AlgebraicGeometry.Quotients.FiniteDescent.CechBaseTmul.Construction.CechBaseChangeMap.map f π ρ g hπ M U).f 0 ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤)] z)) = _
      rw [AlgebraicGeometry.Quotients.FiniteDescent.CechBaseTmul.Construction.CechBaseChangeMap.one_tmul, Normalized.KernelBaseChange.scalarFunctionalBaseChange_tmul, mul_one]
      exact CechAxisBaseChange.cechAxisFunctional_restrictedBaseChange f b g s h U i π ρ hπ hs hb M r hi z
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end

end OAI.RepresentationTheory.Theta.Geometric.CechAxisTensorComparison
