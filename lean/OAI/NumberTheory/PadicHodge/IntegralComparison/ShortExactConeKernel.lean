import OAI.NumberTheory.PadicHodge.PeriodInvariants.MappingConeQuasiIso
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

/-! # Short Exact Cone Kernel -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ShortExactConeKernel

noncomputable section

/-! The cone of the quotient map in a short exact sequence of complexes
is quasi-isomorphic to its kernel shifted by one. The map is obtained
from the genuine cone rotation and the canonical cokernel comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

open _root_.CochainComplex

variable (S : ShortComplex (CochainComplex C ℤ))

def coneMap : mappingCone (mappingCone.inr S.f) ⟶ mappingCone S.g :=
  mappingCone.map (mappingCone.inr S.f) S.g (𝟙 S.X₂)
    (mappingCone.descShortComplex S) (by simp)

def comparison : S.X₁⟦(1 : ℤ)⟧ ⟶ mappingCone S.g :=
  (mappingCone.rotateHomotopyEquiv S.f).hom ≫ coneMap S

theorem coneMap_quasiIso (hS : S.ShortExact) : QuasiIso (coneMap S) :=
  PeriodInvariants.MappingConeQuasiIso.quasiIso_map (mappingCone.inr S.f) S.g (𝟙 S.X₂)
    (mappingCone.descShortComplex S) (by simp) inferInstance
    (mappingCone.quasiIso_descShortComplex hS)

theorem comparison_quasiIso (hS : S.ShortExact) : QuasiIso (comparison S) := by
  have : QuasiIso (coneMap S) := coneMap_quasiIso S hS
  exact quasiIso_comp _ _

def homologyIso (hS : S.ShortExact) (n : ℤ) :
    (S.X₁⟦(1 : ℤ)⟧).homology n ≅ (mappingCone S.g).homology n := by
  have := comparison_quasiIso S hS
  exact isoOfQuasiIsoAt (comparison S) n

variable (T : ShortComplex C)

abbrev single := HomologicalComplex.single C (.up ℤ) 0

def singleComparison : ((ShortExactConeKernel.single.obj T.X₁)⟦(1 : ℤ)⟧) ⟶ mappingCone (ShortExactConeKernel.single.map T.g) :=
  comparison (T.map ShortExactConeKernel.single)

theorem singleComparison_quasiIso (hT : T.ShortExact) :
    QuasiIso (singleComparison T) :=
  comparison_quasiIso (T.map ShortExactConeKernel.single) (hT.map_of_exact ShortExactConeKernel.single)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ShortExactConeKernel
