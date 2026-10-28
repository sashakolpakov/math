import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.NormalizedTrace
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictedGlobalUnit
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.BasisIsomorphisms

/-! # Basis Structure Trace -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BasisStructureTrace

noncomputable section

/-! Compatible algebra traces on a basis of finite free affine opens glue to a structure-sheaf retraction. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u v

variable {X Y : Scheme.{u}} (f : Y ⟶ X) {ι : Type v} (B : ι → X.Opens)
variable (hA : ∀ i, IsAffineOpen (B i)) (hY : ∀ i, IsAffineOpen (f ⁻¹ᵁ B i))
variable {n : ℕ}
variable (b : ∀ i, @Module.Basis (Fin n) Γ(X, B i) Γ(Y, f ⁻¹ᵁ B i) _ _ (f.app (B i)).hom.toModule)
variable (u : Γ(X, ⊤)ˣ)

def affineBasisStructureTraceData :
    HilbertConstruction.Module.MapBasisExtension.ModuleBasisMap B ((Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule Y)) (Line.Bundles.structureModule X) where
  app i := AffineOpen.NormalizedTrace.affineOpenNormalizedTrace f (B i) (RestrictedGlobalUnit.restrictedGlobalUnit u (B i))
  naturality i j h s := by
    have ht := AffineOpen.NormalizedTrace.affineOpenNormalizedTrace_restrict f h (hA j) (hA i) (hY j)
      (b j) (RestrictedGlobalUnit.restrictedGlobalUnit u (B j)) s
    rw [RestrictedGlobalUnit.restrictedGlobalUnit_restrict u h] at ht
    exact ht

variable (hB : Opens.IsBasis (Set.range B))

def affineBasisStructureTrace :
    (Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule Y) ⟶ Line.Bundles.structureModule X :=
  (affineBasisStructureTraceData f B hA hY b u).extend hB

theorem affineBasisStructureTrace_unit (hu : (u : Γ(X, ⊤)) = n) :
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
      affineBasisStructureTrace f B hA hY b u hB = 𝟙 (Line.Bundles.structureModule X) := by
  apply HilbertConstruction.Module.BasisIsomorphisms.moduleMap_eq_of_basis B hB
  intro i
  apply ConcreteCategory.hom_ext
  intro r
  change Γ(X, B i) at r
  change ((affineBasisStructureTraceData f B hA hY b u).extend hB).app (B i) ((f.app (B i)) r) = r
  refine ((affineBasisStructureTraceData f B hA hY b u).extend_app hB i ((f.app (B i)) r)).trans ?_
  exact @Normalized.AlgebraTrace.normalizedAlgebraTrace_algebraMap Γ(X, B i) Γ(Y, f ⁻¹ᵁ B i)
    _ _ (f.app (B i)).hom.toAlgebra n (b i) (RestrictedGlobalUnit.restrictedGlobalUnit u (B i))
    (RestrictedGlobalUnit.restrictedGlobalUnit_val u hu (B i)) r

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BasisStructureTrace
