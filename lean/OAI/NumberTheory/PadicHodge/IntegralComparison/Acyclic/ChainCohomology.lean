import OAI.NumberTheory.PadicHodge.IntegralComparison.ChainResolutionOpposite
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionCohomology

/-! # Chain Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainCohomology

noncomputable section

/-! Actual Ext is computed by an augmented chain resolution whose terms are acyclic for the fixed target. -/

open _root_.CategoryTheory

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (Y : C)
  (P : ChainComplex C ℕ) {Z : C} (ε : P ⟶ (ChainComplex.single₀ C).obj Z) [QuasiIso ε]
  (hP : ∀ a q, Subsingleton (Ext.{z} (P.X a) Y (q + 1)))

def complex : CochainComplex (ModuleCat.{z} R) ℕ :=
  Contravariant.Resolution.Comparison.complex R Y P.op

def homologyIso (i : ℕ) : (complex R Y P).homology i ≅ ModuleCat.of R (Ext.{z} Z Y i) := by
  let : QuasiIso (ChainResolutionOpposite.augmentation P ε) :=
    ChainResolutionOpposite.augmentation_quasiIso P ε
  exact Contravariant.ResolutionCohomology.homologyIso R Y P.op
    (ChainResolutionOpposite.augmentation P ε) hP i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainCohomology
