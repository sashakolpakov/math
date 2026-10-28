import OAI.NumberTheory.PadicHodge.PeriodInvariants.ExactComplexQuasiIso
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Mapping Cone Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.MappingConeQuasiIso

noncomputable section

/-! # Commutative squares of quasi-isomorphisms induce quasi-isomorphisms of cones and cocones -/

open _root_.CategoryTheory

attribute [local instance] Abelian.hasFiniteBiproducts

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
  (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (h : φ₁ ≫ b = a ≫ φ₂)

def shortComplexMap : CochainComplex.mappingCone.triangleRotateShortComplex φ₁ ⟶
    CochainComplex.mappingCone.triangleRotateShortComplex φ₂ where
  τ₁ := b
  τ₂ := CochainComplex.mappingCone.map φ₁ φ₂ a b h
  τ₃ := a⟦(1 : ℤ)⟧'
  comm₁₂ := (CochainComplex.mappingCone.triangleMap φ₁ φ₂ a b h).comm₂.symm
  comm₂₃ := (CochainComplex.mappingCone.triangleMap φ₁ φ₂ a b h).comm₃.symm

theorem quasiIso_map (ha : QuasiIso a) (hb : QuasiIso b) :
    QuasiIso (CochainComplex.mappingCone.map φ₁ φ₂ a b h) := by
  have hS₁ := HomologicalComplex.shortExact_of_degreewise_shortExact
    (CochainComplex.mappingCone.triangleRotateShortComplex φ₁)
    (fun i => (CochainComplex.mappingCone.triangleRotateShortComplexSplitting φ₁ i).shortExact)
  have hS₂ := HomologicalComplex.shortExact_of_degreewise_shortExact
    (CochainComplex.mappingCone.triangleRotateShortComplex φ₂)
    (fun i => (CochainComplex.mappingCone.triangleRotateShortComplexSplitting φ₂ i).shortExact)
  exact ExactComplexQuasiIso.Short.middle (shortComplexMap φ₁ φ₂ a b h) hS₁ hS₂ hb
    ((CochainComplex.quasiIso_shift_iff a 1).mpr ha)

def coconeMap : CochainComplex.mappingCocone φ₁ ⟶ CochainComplex.mappingCocone φ₂ :=
  (CochainComplex.mappingCone.map φ₁ φ₂ a b h)⟦(-1 : ℤ)⟧'

theorem quasiIso_coconeMap (ha : QuasiIso a) (hb : QuasiIso b) :
    QuasiIso (coconeMap φ₁ φ₂ a b h) :=
  (CochainComplex.quasiIso_shift_iff _ (-1)).mpr (quasiIso_map φ₁ φ₂ a b h ha hb)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.MappingConeQuasiIso
