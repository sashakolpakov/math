import Mathlib

/-! # Site Cocontinuity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SiteCocontinuity

noncomputable section

/-!
# IntegralComparison: cocontinuity from pullbacks of generating covers

It suffices to lift the pullback of every generating covering family.
The proof follows the actual inductive construction of the generated
Grothendieck topology, including pullbacks and transitivity.
-/

open _root_.CategoryTheory

universe u v u' v'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (F : C ⥤ D) (J : GrothendieckTopology C) (K : Precoverage D)

theorem cocontinuous_of_generating_pullbacks
    (h : ∀ {U : D} {V : C} (R : Presieve U), R ∈ K U → ∀ (a : F.obj V ⟶ U),
      ((Sieve.generate R).pullback a).functorPullback F ∈ J V) :
    F.IsCocontinuous J K.toGrothendieck := by
  have aux : ∀ {U : D} {S : Sieve U}, S ∈ K.toGrothendieck U →
      ∀ (V : C) (a : F.obj V ⟶ U), (S.pullback a).functorPullback F ∈ J V := by
    intro U S hS
    induction hS with
    | of U R hR => exact fun _ a => h R hR a
    | top U =>
      intro V a
      simpa only [Sieve.pullback_top, Sieve.functorPullback_top] using J.top_mem V
    | pullback U S hS W b ih =>
      intro V a
      simpa only [← Sieve.pullback_comp] using ih V (a ≫ b)
    | transitive U S R hS hR ihS ihR =>
      intro V a
      apply J.transitive (ihS V a)
      intro W b hb
      have hi := ihR hb W (𝟙 (F.obj W))
      simpa only [Sieve.pullback_id, Sieve.pullback_comp, Sieve.functorPullback_pullback] using hi
  constructor
  intro U S hS
  simpa only [Sieve.pullback_id] using aux hS U (𝟙 (F.obj U))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SiteCocontinuity
