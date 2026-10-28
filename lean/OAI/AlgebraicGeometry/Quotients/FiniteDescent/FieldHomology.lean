import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.QuasiIso
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Finiteness.Basic

/-! # Field Homology -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.FieldHomology

noncomputable section

/-! A short complex of vector spaces has a projection onto its homology,
viewed as a short complex with zero differentials. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace Construction.FieldHomologyProjection

variable {K : Type u} [Field K] (S : ShortComplex (ModuleCat.{u} K))

abbrev H : ModuleCat.{u} K := S.moduleCatLeftHomologyData.H

def projection : S.X₂ ⟶ FieldHomologyProjection.H S :=
  ModuleCat.ofHom (S.moduleCatLeftHomologyData.π.hom.comp
    S.moduleCatLeftHomologyData.i.hom.leftInverse)

theorem cycles_projection :
    S.moduleCatLeftHomologyData.i ≫ projection S = S.moduleCatLeftHomologyData.π := by
  apply ModuleCat.hom_ext
  change S.moduleCatLeftHomologyData.π.hom.comp
    (S.moduleCatLeftHomologyData.i.hom.leftInverse.comp S.moduleCatLeftHomologyData.i.hom) = _
  rw [LinearMap.leftInverse_comp_of_inj (LinearMap.ker_eq_bot.mpr
    ((ModuleCat.mono_iff_injective _).mp inferInstance)), LinearMap.comp_id]

theorem incoming_projection : S.f ≫ projection S = 0 := by
  rw [← S.moduleCatLeftHomologyData.f'_i, Category.assoc, cycles_projection]
  exact S.moduleCatLeftHomologyData.wπ

def target : ShortComplex (ModuleCat.{u} K) :=
  ShortComplex.mk (0 : ModuleCat.of K (Fin 0 → K) ⟶ FieldHomologyProjection.H S)
    (0 : FieldHomologyProjection.H S ⟶ ModuleCat.of K (Fin 0 → K)) (by simp)

def map : S ⟶ target S where
  τ₁ := 0
  τ₂ := projection S
  τ₃ := 0
  comm₁₂ := by simpa only [target, zero_comp] using (incoming_projection S).symm
  comm₂₃ := by simp [target]

def data : ShortComplex.LeftHomologyMapData (map S) S.moduleCatLeftHomologyData
    (ShortComplex.LeftHomologyData.ofZeros (target S) rfl rfl) where
  φK := S.moduleCatLeftHomologyData.π
  φH := 𝟙 _
  commi := by
    change S.moduleCatLeftHomologyData.π ≫ 𝟙 _ =
      S.moduleCatLeftHomologyData.i ≫ projection S
    rw [Category.comp_id, cycles_projection]
  commf' := by simp
  commπ := rfl

theorem quasiIso : ShortComplex.QuasiIso (map S) := by
  apply (data S).quasiIso_iff.mpr
  change IsIso (𝟙 _)
  infer_instance

theorem finite [Module.Finite K S.homology] : Module.Finite K (FieldHomologyProjection.H S) :=
  Module.Finite.equiv S.moduleCatHomologyIso.toLinearEquiv

end Construction.FieldHomologyProjection

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.FieldHomology
