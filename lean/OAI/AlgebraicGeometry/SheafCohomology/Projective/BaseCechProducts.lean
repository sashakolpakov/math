/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import Mathlib.Algebra.Category.ModuleCat.Products
import OAI.AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic

/-! # Base Cech Products -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechProducts.Scheme.Modules

noncomputable section

open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u

/-- A degree of the base-linear Cech complex is the concrete dependent
product of its intersection-section factors. -/
def baseCechXIsoPi {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) {ι : Type u}
    (U : ι → X.Opens) (n : ℕ) : (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X n ≅
      ModuleCat.of Γ(S, (⊤ : S.Opens))
        (∀ i : Fin (n + 1) → ι, Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n i) :=
  ModuleCat.piIsoPi _

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechProducts.Scheme.Modules
