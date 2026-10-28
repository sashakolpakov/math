import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.LogarithmicHomotopy

/-! # Logarithmic Homotopy Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PD.LogarithmicHomotopyNaturality

noncomputable section

/-! The explicit PD logarithmic primitive commutes with the original
PD form maps at a fixed truncation length. Thus its restrictions are
compatible before passage to cohomology. -/
open scoped BigOperators
namespace Logarithm
universe u
variable {A B : Type u} [CommRing A] [CommRing B]
  {I : Ideal A} {δI : DividedPowers I} {J : Ideal B} {δJ : DividedPowers J}

theorem map_logarithm (f : A →+* B) (hf : DividedPowers.IsDPMorphism δI δJ f)
    (N : ℕ) {x : A} (hx : x ∈ I) :
    f (Logarithm.logarithm I δI N x) = Logarithm.logarithm J δJ N (f x) := by
  simp only [Logarithm.logarithm, map_sum, map_mul, map_pow, map_neg, map_one, map_natCast,
    hf.map_dpow hx]

end Logarithm

namespace Forms
open _root_.CategoryTheory
universe u
variable {R : Type u} [CommRing R] {A B : CommAlgCat.{u} R}
  {I : Ideal A} {δI : DividedPowers I} {J : Ideal B} {δJ : DividedPowers J}
  (f : A ⟶ B) (hf : DividedPowers.IsDPMorphism δI δJ f.hom.toRingHom)

theorem formMap_dlog (u : Aˣ) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap f hf 1 (LogarithmicForms.dlog R A I δI u) =
      LogarithmicForms.dlog R B J δJ (Units.map f.hom.toMonoidHom u) :=
  LogarithmicNaturality.Forms.addMap_dlog R R A B I δI J δJ f.hom.toRingHom
    (fun j => (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap f hf j).toAddMonoidHom)
    (fun j a v => AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_symbol f hf j a v) u

theorem formMap_primitiveOne (N : ℕ) (u v : Aˣ) (huv : (v : A) - (u : A) ∈ I) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap f hf 0 (LogarithmicHomotopy.Forms.primitiveOne R A I δI N u v) =
      LogarithmicHomotopy.Forms.primitiveOne R B J δJ N (Units.map f.hom.toMonoidHom u)
        (Units.map f.hom.toMonoidHom v) := by
  change AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap f hf 0 (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δI
    (Logarithm.logarithm I δI N ((↑(v * u⁻¹) : A) - 1))
      (fun i : Fin 0 => i.elim0)) = _
  rw [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_symbol]
  have hlog := Logarithm.map_logarithm f.hom.toRingHom hf N (LogarithmicHomotopy.Forms.ratio_mem A I u v huv)
  change f (Logarithm.logarithm I δI N ((↑(v * u⁻¹) : A) - 1)) = _ at hlog
  rw [hlog]
  change AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R B J δJ _ _ = AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R B J δJ _ _
  congr 1
  · congr 1
    simp only [map_sub, map_one, Units.val_mul, map_mul, Units.coe_map]
    rfl
  · ext i
    exact i.elim0

theorem formMap_logarithmicPrimitive (N n : ℕ) (u v : Fin (n + 1) → Aˣ)
    (huv : ∀ i, (v i : A) - (u i : A) ∈ I) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap f hf n (LogarithmicHomotopy.Forms.logarithmicPrimitive R A I δI N n u v) =
      LogarithmicHomotopy.Forms.logarithmicPrimitive R B J δJ N n
        (fun i => Units.map f.hom.toMonoidHom (u i))
        (fun i => Units.map f.hom.toMonoidHom (v i)) := by
  induction n with
  | zero => exact formMap_primitiveOne f hf N (u 0) (v 0) (huv 0)
  | succ n ih =>
      rw [LogarithmicHomotopy.Forms.logarithmicPrimitive, LogarithmicHomotopy.Forms.logarithmicPrimitive, map_add, map_zsmul,
        DeRhamProductNaturality.Wedge.formMap_wedge f hf n 1, DeRhamProductNaturality.Wedge.formMap_wedge f hf (n + 1) 0,
        ih _ _ (fun i => huv i.castSucc),
        formMap_dlog f hf,
        LogarithmicFrame.Forms.formMap_logarithmicWedge f hf,
        formMap_primitiveOne f hf N _ _ (huv (Fin.last (n + 1)))]

end Forms

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PD.LogarithmicHomotopyNaturality
