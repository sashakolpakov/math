import OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantSheaf
import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.ResolutionHom

/-! # Acyclic Resolution Sections -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Module.AcyclicResolutionSections.ModuleAcyclicResolutionSections

noncomputable section

/-! Exact sections of an actual resolution by coefficient-Ext-acyclic module sheaves. -/

open _root_.CategoryTheory Abelian Limits Opposite

variable (R : Type) [CommRing R] (X : TopCat.{0})

local instance : HasExt.{1} (ConstantSheaf.ConstantSheafSections.Sheaves R X) := HasExt.standard _

variable (K : CochainComplex (ConstantSheaf.ConstantSheafSections.Sheaves R X) ℕ)
  {F : ConstantSheaf.ConstantSheafSections.Sheaves R X} (e : F ⟶ K.X 0)
  (w : e ≫ K.d 0 1 = 0)

theorem exact_succ [Mono e]
    (haug : (ShortComplex.mk e (K.d 0 1) w).Exact)
    (hpos : ∀ n, (AlgebraicGeometry.Comparison.Betti.Acyclic.ResolutionCycles.Ext.resolutionSequence K n).Exact)
    (hF : ∀ q, Subsingleton (Ext.{1} (ConstantSheaf.ConstantSheafSections.coefficient R X) F (q + 1)))
    (hK : ∀ p q, Subsingleton (Ext.{1} (ConstantSheaf.ConstantSheafSections.coefficient R X) (K.X p) (q + 1)))
    (n : ℕ) (x : (K.X (n + 1)).obj.obj (op ⊤))
    (hx : (K.d (n + 1) (n + 2)).hom.app (op ⊤) x = 0) :
    ∃ y : (K.X n).obj.obj (op ⊤), (K.d n (n + 1)).hom.app (op ⊤) y = x := by
  let z := (ConstantSheaf.ConstantSheafSections.linearEquiv R X (K.X (n + 1))).symm x
  have hz : z ≫ K.d (n + 1) (n + 2) = 0 := by
    apply (ConstantSheaf.ConstantSheafSections.linearEquiv R X (K.X (n + 2))).injective
    rw [ConstantSheaf.ConstantSheafSections.naturality, map_zero]
    exact (congrArg ((K.d (n + 1) (n + 2)).hom.app (op ⊤))
      ((ConstantSheaf.ConstantSheafSections.linearEquiv R X (K.X (n + 1))).apply_symm_apply x)).trans hx
  obtain ⟨y, hy⟩ := AlgebraicGeometry.Comparison.Betti.Acyclic.ResolutionHom.Ext.acyclicResolution_hom_exact_succ
    (ConstantSheaf.ConstantSheafSections.coefficient R X) K e w haug hpos hF hK n z hz
  refine ⟨ConstantSheaf.ConstantSheafSections.linearEquiv R X (K.X n) y, ?_⟩
  rw [← ConstantSheaf.ConstantSheafSections.naturality, hy]
  exact (ConstantSheaf.ConstantSheafSections.linearEquiv R X (K.X (n + 1))).apply_symm_apply x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Module.AcyclicResolutionSections.ModuleAcyclicResolutionSections
