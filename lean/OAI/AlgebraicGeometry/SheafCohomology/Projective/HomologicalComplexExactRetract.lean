/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Homological Complex Exact Retract -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.HomologicalComplexExactRetract.HomologicalComplex

open _root_.HomologicalComplex

/-!
# Exactness of retracts of homological complexes

Exactness at a fixed degree descends from a homological complex to any chain-level retract.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {ι : Type w} {c : ComplexShape ι}

theorem ExactAt.of_retract
    {K L : HomologicalComplex C c} {i : ι}
    [K.HasHomology i] [L.HasHomology i]
    (hK : K.ExactAt i) (f : L ⟶ K) (g : K ⟶ L)
    (hfg : f ≫ g = 𝟙 L) :
    L.ExactAt i := by
  rw [exactAt_iff_isZero_homology] at hK ⊢
  rw [IsZero.iff_id_eq_zero]
  calc
    𝟙 (L.homology i) = homologyMap (𝟙 L) i :=
      (homologyMap_id L i).symm
    _ = homologyMap (f ≫ g) i :=
      congrArg (fun h : L ⟶ L => homologyMap h i) hfg.symm
    _ = homologyMap f i ≫ homologyMap g i :=
      homologyMap_comp f g i
    _ = 0 := by rw [hK.eq_of_tgt (homologyMap f i) 0, zero_comp]

end OAI.AlgebraicGeometry.SheafCohomology.Projective.HomologicalComplexExactRetract.HomologicalComplex
