import OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverEffectiveDescent
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Over Kernel Pair Factor -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverKernelPairFactor

noncomputable section

/-! Actual kernel-pair equations descend morphisms over the original
base, including endomorphisms preserving the given relation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem over_factor_of_kernelPair {S W : Scheme.{0}} {X Y Z : Over S}
    (q : X ⟶ Y) [EffectiveEpi q.left] (s t : W ⟶ X.left)
    (hq : IsKernelPair q.left s t) (f : X ⟶ Z) (hf : s ≫ f.left = t ≫ f.left) :
    ∃! d : Y ⟶ Z, q ≫ d = f := by
  apply OverEffectiveDescent.over_factor_of_effectiveEpi q f
  intro T a b hab
  let l := hq.lift a.left b.left (congrArg Over.Hom.left hab)
  have h := congrArg (fun m => l ≫ m) hf
  apply Over.OverMorphism.ext
  change a.left ≫ f.left = b.left ≫ f.left
  simpa only [← Category.assoc, l, hq.lift_fst, hq.lift_snd] using h

theorem over_endomorphism_descends_of_relation {S W : Scheme.{0}} {X Y : Over S}
    (q : X ⟶ Y) [EffectiveEpi q.left] (s t : W ⟶ X.left)
    (hq : IsKernelPair q.left s t) (m : X ⟶ X) (r : W ⟶ W)
    (hs : r ≫ s = s ≫ m.left) (ht : r ≫ t = t ≫ m.left) :
    ∃! d : Y ⟶ Y, q ≫ d = m ≫ q := by
  apply over_factor_of_kernelPair q s t hq (m ≫ q)
  change s ≫ m.left ≫ q.left = t ≫ m.left ≫ q.left
  rw [← Category.assoc, ← hs, Category.assoc, hq.w, ← Category.assoc, ht, Category.assoc]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverKernelPairFactor
