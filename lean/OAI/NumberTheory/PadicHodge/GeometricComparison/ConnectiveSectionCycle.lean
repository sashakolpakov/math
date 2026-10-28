import OAI.NumberTheory.PadicHodge.GeometricComparison.ConnectiveDerivedEquiv
import OAI.NumberTheory.PadicHodge.GeometricComparison.SingleMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantSheaf

/-! # Connective Section Cycle -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ConnectiveSectionCycle.ConnectiveSectionKernel

noncomputable section

/-! Degree-zero derived global sections of a connective complex are the actual kernel on global sections. No higher-cohomology vanishing is assumed. -/

open _root_.CategoryTheory Opposite

variable (R : Type) [CommRing R] (X : TopCat.{0})

local notation "V" => OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantSheaf.ConstantSheafSections.Sheaves R X
local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantSheaf.ConstantSheafSections.coefficient R X

local instance : HasDerivedCategory.{1} V := HasDerivedCategory.standard _

def sectionKernel (K : CochainComplex V ℤ) :
    Submodule R ((K.X 0).obj.obj (op ⊤)) := ((K.d 0 1).hom.app (op ⊤)).hom.ker

def cycleEquiv (K : CochainComplex V ℤ) :
    SingleMap.SingleMapCycles.cycles R A K 0 ≃ₗ[R] sectionKernel R X K where
  toFun f := ⟨ConstantSheaf.ConstantSheafSections.linearEquiv R X (K.X 0) f.val, by
    have h := ConstantSheaf.ConstantSheafSections.naturality R X f.val (K.d 0 1)
    change (K.d 0 1).hom.app (op ⊤) (ConstantSheaf.ConstantSheafSections.linearEquiv R X (K.X 0) f.val) = 0
    rw [← h]
    have hf : f.val ≫ K.d 0 1 = 0 := f.property
    rw [hf, map_zero]⟩
  invFun s := ⟨(ConstantSheaf.ConstantSheafSections.linearEquiv R X (K.X 0)).symm s.val, by
    change (ConstantSheaf.ConstantSheafSections.linearEquiv R X (K.X 0)).symm s.val ≫ K.d 0 1 = 0
    apply (ConstantSheaf.ConstantSheafSections.linearEquiv R X (K.X 1)).injective
    rw [ConstantSheaf.ConstantSheafSections.naturality, LinearEquiv.apply_symm_apply, map_zero]
    exact s.property⟩
  left_inv f := Subtype.ext ((ConstantSheaf.ConstantSheafSections.linearEquiv R X (K.X 0)).symm_apply_apply f.val)
  right_inv s := Subtype.ext ((ConstantSheaf.ConstantSheafSections.linearEquiv R X (K.X 0)).apply_symm_apply s.val)
  map_add' f g := Subtype.ext ((ConstantSheaf.ConstantSheafSections.linearEquiv R X (K.X 0)).map_add f.val g.val)
  map_smul' r f := Subtype.ext ((ConstantSheaf.ConstantSheafSections.linearEquiv R X (K.X 0)).map_smul r f.val)

def equiv (K : CochainComplex V ℤ) [K.IsStrictlyGE 0] :
    ((DerivedCategory.singleFunctor V 0).obj A ⟶ DerivedCategory.Q.obj K) ≃ₗ[R]
      sectionKernel R X K :=
  (ConnectiveDerivedEquiv.ConnectiveDerivedEquivalence.equiv R (X := (CochainComplex.singleFunctor V 0).obj A)
    (Y := K) 0).symm.trans ((SingleMap.SingleMapCycles.equiv R A K 0).trans (cycleEquiv R X K))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ConnectiveSectionCycle.ConnectiveSectionKernel
